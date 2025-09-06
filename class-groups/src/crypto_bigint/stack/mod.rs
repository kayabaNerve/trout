use core::ops::Neg;

use zeroize::Zeroize;

use crypto_bigint::{CtEq, CtSelect, NonZero, Integer, Uint};

use crate::Table;

mod numbers;
use numbers::*;

// 2048-bit fundamental discriminant with 256-bit subgroup = 2560-bit discriminant
/*
  We use a further 128 bits for the misc additions/shifts we perform during steps. While ideally,
  we'd only use a further 64 bits, we need an even amount of limbs inside crypto-bigint.
*/
const BITS: u32 = 2688;

// We use `U` to represent `a` which is bounded by the square root of the absolute value of the
// discriminant, so its bit-length will be half of the absolute value of the discriminant's
const A_BITS: u32 = BITS / 2;
type U = Uint<{ crypto_bigint::nlimbs(A_BITS) }>;
// We use `I` to represent `b` which is bounded `-a < b < a`, so its absolute value fits into the
// same amount of bits as `a` does
type I = IStruct<Uint<{ crypto_bigint::nlimbs(A_BITS) }>>;

type WideU = Uint<{ crypto_bigint::nlimbs(BITS) }>;
type WideI = IStruct<WideU>;

type WideWideU = Uint<{ crypto_bigint::nlimbs(2 * BITS) }>;

/// A constant-time element of a class group, implemented via crypto-bigint's `Uint, Int`.
///
/// This is implemented in time variable to the discriminant yet constant to `a, b`. This prevents
/// timing analysis from leaking the elements being composed. It is only recommended for provers as
/// it has a significant performance overhead to other backends, which verifiers should take
/// advantage of.
///
/// The usage of `Uint, Int` means these elements live on the stack and are fixed size. They
/// accordingly only support discriminants of bounded size. Using a larger discriminant may cause a
/// runtime panic. The officially supported bound is a 2560-bit discriminant.
// TODO: Parameterize bits at a higher level
#[derive(Clone, Debug)]
pub struct CryptoBigintStackElement {
  a: U,
  b: I,
  discriminant: WideI,
}

impl PartialEq for CryptoBigintStackElement {
  fn eq(&self, other: &Self) -> bool {
    (self.a.ct_eq(&other.a) & self.b.ct_eq(&other.b) & self.discriminant.ct_eq(&other.discriminant))
      .into()
  }
}
impl Eq for CryptoBigintStackElement {}

impl Zeroize for CryptoBigintStackElement {
  fn zeroize(&mut self) {
    // Zeroize
    self.a.zeroize();
    self.b.zeroize();

    // Set to the identity
    self.a = U::ONE;
    self.b = I::one();
  }
}

impl crypto_bigint::CtSelect for CryptoBigintStackElement {
  fn ct_select(&self, b: &Self, choice: crypto_bigint::Choice) -> Self {
    Self {
      a: U::ct_select(&self.a, &b.a, choice),
      b: I::ct_select(&self.b, &b.b, choice),
      // Safe since `Element` is documented to have undefined behavior when mixed across class
      // groups
      discriminant: self.discriminant,
    }
  }
}

impl CryptoBigintStackElement {
  fn reduce(log_2_a_bound: u32, a: WideU, b: WideI, discriminant: WideI) -> Self {
    let b_decomposed = (!b.positive(), *b.abs());
    let (a, b_decomposed, _c) = super::reduce(log_2_a_bound, a, b_decomposed, discriminant.abs());
    let a = a.split().0;
    let mut b = IStruct::from(b_decomposed.1.split().0);
    b = <_>::ct_select(&b, &-b, b_decomposed.0);
    Self { a, b, discriminant }
  }
}

impl crate::Element for CryptoBigintStackElement {
  const MAX_TABLE_BITS: u32 = 12;

  fn is_identity(&self) -> subtle::Choice {
    (self.a.ct_eq(&U::ONE) & self.b.ct_eq(&I::one())).into()
  }

  // Allegedly, Arndt's method, as specified on the Wikipedia page for binary quadratic forms
  fn add(&self, other: &Self) -> CryptoBigintStackElement {
    let B_mu: I = (self.b + other.b).half();

    // \gcd_1
    let (g_1, u_1, v_1, _) = self.a.extended_gcd(other.a);
    // \gcd_2
    let (e, _v_2, _u_2, A1_A2_xgcd_div_e) = g_1.extended_gcd(B_mu.into_abs());
    let e = NonZero::new(e).unwrap();
    let A1_div_e: U = self.a / e;
    let A2_div_e: U = other.a / e;
    let A: WideU = A1_div_e.concatenating_mul(&A2_div_e);

    let mod_1: U = A1_div_e.overflowing_shl_vartime(1).unwrap();
    let mod_2: U = A2_div_e.overflowing_shl_vartime(1).unwrap();
    let two_A: WideU = A.overflowing_shl_vartime(1).unwrap();
    let mut mod_3 = two_A;

    let congruence_1 = self.b % mod_1;
    let congruence_2 = other.b % mod_2;
    let e = e.get();
    let wide_e = WideU::from((e, U::ZERO));

    // We drop the remainder here because `e` is explicitly a divisor of `B_mu`
    let B_mu_div_e = (B_mu / e).0;

    let (congruence_3, g_3) = {
      let congruence_3_rhs = {
        let congruence_3_rhs_numerator = self.discriminant + (self.b * other.b);
        let (congruence_3_rhs_mul_2, rem) = congruence_3_rhs_numerator / wide_e;
        debug_assert!(bool::from(rem.is_zero()));
        congruence_3_rhs_mul_2.half()
      } % mod_3;

      let congruence_3_lhs_factor = B_mu_div_e.widen::<WideU>();

      /*
        We have `ax congruent to b mod c`.

        We can't scale `b` by `a**-1` as `a` may not have a multiplicative inverse `mod c`. We
        instead scale `a` by `u` where for `g = 1`, `a * u congruent to 1 mod c` (so `u` would be
        the multiplicative inverse of `a` if `g = 1`). When `g != 1`, this generalizes as
        `a * u congruent to g mod c`. Scaling `a` by `u` accordingly produces `a * a**-1 * g`,
        which we convert to `a * a**-1` via integer division by `g`.
      */

      // \gcd_3
      let (g, u, mod_3_div_g): (WideU, WideU, WideU) =
        congruence_3_lhs_factor.abs().extended_gcd_part(mod_3);
      let wide_g = WideWideU::from((g, WideU::ZERO));
      let (res, rem): (WideWideU, WideWideU) =
        congruence_3_rhs.concatenating_mul(&u).div_rem(&NonZero::new(wide_g).unwrap());
      debug_assert!(bool::from(rem.is_zero()));
      mod_3 = mod_3_div_g;

      // Reduce res by the modulus
      let wide_mod_3 = WideWideU::from((mod_3, WideU::ZERO));
      let res = res % wide_mod_3;
      // Since this modulus only used the low bits, this only has low bits
      let res = res.split().0;
      let res = <_>::ct_select(&(mod_3 - res), &res, congruence_3_lhs_factor.positive());
      (res, g)
    };

    // CRT generalized for coprime moduli
    fn crt<const LIMBS: usize, const TWICE_LIMBS: usize, const THRICE_LIMBS: usize>(
      congruence_1: Uint<LIMBS>,
      mod_1: Uint<LIMBS>,
      congruence_2: Uint<LIMBS>,
      mod_2: Uint<LIMBS>,
      mod_1_mod_2_xgcd: (Uint<LIMBS>, Uint<LIMBS>, IStruct<Uint<LIMBS>>, Uint<LIMBS>),
    ) -> (IStruct<Uint<THRICE_LIMBS>>, Uint<TWICE_LIMBS>) {
      let (g, u, v, mod_1_div_g) = mod_1_mod_2_xgcd;
      debug_assert!(bool::from((congruence_1 % g).ct_eq(&(congruence_2 % g))));

      let M = mul_arbitrary_uints::<LIMBS, LIMBS, TWICE_LIMBS>(mod_1_div_g, mod_2);
      let x1: IStruct<Uint<{ THRICE_LIMBS }>> =
        IStruct::<Uint<TWICE_LIMBS>>::from(mul_arbitrary_uints(congruence_1, mod_2)).mul_i_uint(v);
      let x2 = mul_arbitrary_uints::<TWICE_LIMBS, LIMBS, THRICE_LIMBS>(
        mul_arbitrary_uints::<LIMBS, LIMBS, TWICE_LIMBS>(congruence_2, mod_1),
        u,
      );
      let x = x1 + x2;

      let g_words = g.as_words();
      let mut wide_g = Uint::<{ THRICE_LIMBS }>::ZERO;
      wide_g.as_mut_words()[.. g_words.len()].copy_from_slice(g_words);
      let (x, rem) = x / wide_g;
      debug_assert!(bool::from(rem.is_zero()));

      (x, M)
    }

    // \gcd_4
    let mod_1_mod_2_xgcd = ((g_1 / e).overflowing_shl_vartime(1).unwrap(), u_1, v_1, self.a / g_1);
    #[cfg(debug_assertions)]
    {
      let actual = mod_1.extended_gcd(mod_2);
      debug_assert_eq!(mod_1_mod_2_xgcd.0, actual.0);
      debug_assert_eq!(mod_1_mod_2_xgcd.3, actual.3);
      debug_assert_eq!(mod_1_mod_2_xgcd.1, actual.1);
      debug_assert_eq!(bool::from(mod_1_mod_2_xgcd.2.positive()), bool::from(actual.2.positive()));
      debug_assert_eq!(mod_1_mod_2_xgcd.2.abs(), actual.2.abs());
    }
    let (wide_congruence_12, mod_12): (_, WideU) =
      crt::<
        { crypto_bigint::nlimbs(BITS / 2) },
        { crypto_bigint::nlimbs(BITS) },
        { crypto_bigint::nlimbs(BITS + (BITS / 2)) },
      >(congruence_1, mod_1, congruence_2, mod_2, mod_1_mod_2_xgcd);

    let mut wide_mod_12 = Uint::<{ crypto_bigint::nlimbs(BITS + (BITS / 2)) }>::ZERO;
    let mod_12_words = mod_12.as_words();
    wide_mod_12.as_mut_words()[.. mod_12_words.len()].copy_from_slice(mod_12_words);
    let wide_congruence_12 = wide_congruence_12 % wide_mod_12;

    let mut congruence_12 = WideU::ZERO;
    let wide_words_len = congruence_12.as_words().len();
    congruence_12.as_mut_words().copy_from_slice(&wide_congruence_12.as_words()[.. wide_words_len]);

    /*
    let gcd_5 = {
      let g_5 = two_A / g_3 / Uint::from((A1_A2_xgcd_div_e, Uint::ZERO));
      let a_apo = IStruct::from(v_2);
      let b_denom = Uint::from((B_mu.into_abs(), Uint::ZERO)).div_rem(&NonZero::new(g_3).unwrap());
      debug_assert_eq!(b_denom.1, Uint::ZERO);
      // This is safe to split as the numerator was only of size U, so this WideU is a U
      let b_denom = b_denom.0.split();
      debug_assert_eq!(b_denom.1, Uint::ZERO);
      let b_denom = b_denom.0;

      let b = u_2 * b_denom;
      let gcd_g1_g3 = (a_apo * g_1).widen::<WideWideU>() + (b * g_3);
      debug_assert!(bool::from(gcd_g1_g3.positive()));
      let gcd_g1_g3 = gcd_g1_g3
        .into_abs()
        .div_rem(&NonZero::new(Uint::from((Uint::from((e, Uint::ZERO)), Uint::ZERO))).unwrap());
      debug_assert_eq!(gcd_g1_g3.1, Uint::ZERO);
      let gcd_g1_g3 = gcd_g1_g3.0;
      let _g_1: U = g_1;
      let _g_3: WideU = g_3;
      // Reduce from WideWideU to U since this is the GCD of a (U, WideU)
      // This is only true if the U is non-zero, which it is as the output of a GCD
      let gcd_g1_g3 = gcd_g1_g3.split().0.split().0;

      // TODO: We need to calculate this without a call to `bingcd` somehow
      let gcd_e_g3 = Uint::from((e, Uint::ZERO)).gcd(&g_3).split().0;
      let gcd_g1_g3 = gcd_g1_g3.concatenating_mul(&gcd_e_g3);
      debug_assert_eq!(Uint::from((g_1 / e, Uint::ZERO)).extended_gcd(g_3).0, Uint::ONE);
      debug_assert_eq!(Uint::from((g_1, Uint::ZERO)).extended_gcd(g_3).0, gcd_g1_g3);

      let a_apo_apo = a_apo;
      let b_apo_apo = b / Uint::from((e, Uint::ZERO));
      debug_assert_eq!(b_apo_apo.1, Uint::ZERO);
      let b_apo_apo = b_apo_apo.0;
      debug_assert!(bool::from(
        ((a_apo_apo * (g_1 / e)).widen::<WideWideU>() + (b_apo_apo * IStruct::from(g_3)))
          .ct_eq(&IStruct::from(gcd_g1_g3).widen::<WideWideU>())
      ));

      let u_5 = b_apo_apo % ((two_A / g_3) / g_5);

      let x = Uint::from((g_1 / e, Uint::ZERO));
      let v_5_mod = (two_A / x) / g_5;
      let v_5 = a_apo_apo.widen::<WideU>() % v_5_mod;
      // We need to negate v_5 if u_5 is non-zero
      let v_5 = <_>::ct_select(
        &IStruct::from(v_5),
        &-IStruct::from(v_5_mod - v_5),
        !u_5.ct_eq(&Uint::ZERO),
      );
      let v_5 =
        <_>::ct_select(&v_5, &IStruct::from(Uint::ZERO), v_5.ct_eq(&-IStruct::from(v_5_mod)));

      // Finally, if d / x == d / y, we normalize to (1, 0)
      let x_eq_y = x.ct_eq(&g_3);
      let u_5 = <_>::ct_select(&u_5, &Uint::ONE, x_eq_y);
      let v_5 = <_>::ct_select(&v_5, &IStruct::from(Uint::ZERO), x_eq_y);

      let res = (g_5, u_5, v_5, v_5_mod);

      #[cfg(debug_assertions)]
      {
        let xgcd = mod_12.extended_gcd(mod_3);
        debug_assert_eq!(res.0, xgcd.0);
        debug_assert_eq!(res.1, xgcd.1);
        debug_assert!(bool::from(res.2.ct_eq(&xgcd.2)));
        debug_assert_eq!(res.3, xgcd.3);
      }

      res
    };
    */
    let gcd_5 = {
      let xgcd = mod_12.extended_gcd(mod_3);
      debug_assert_eq!(two_A / g_3 / Uint::from((A1_A2_xgcd_div_e, Uint::ZERO)), xgcd.0);
      xgcd
    };
    let (x, _mod_123): (_, WideWideU) = crt::<
      { crypto_bigint::nlimbs(BITS) },
      { crypto_bigint::nlimbs(2 * BITS) },
      { crypto_bigint::nlimbs(3 * BITS) },
    >(congruence_12, mod_12, congruence_3, mod_3, gcd_5);

    let mut wide_two_A = Uint::<{ crypto_bigint::nlimbs(3 * BITS) }>::ZERO;
    let two_A_words = two_A.as_words();
    wide_two_A.as_mut_words()[.. two_A_words.len()].copy_from_slice(two_A_words);
    let wide_B = x % wide_two_A;

    let mut B = WideU::ZERO;
    B.as_mut_words().copy_from_slice(&wide_B.as_words()[.. wide_words_len]);

    // Since `A = (A_1 / e) * (A_2 / e)`, where `e = gcd(A_1, A_2, B_mu)`, we assume `e = 1` and
    // the bound on `log_2(A)` becomes `log_2(A_1 * A_2)`
    let log_2_a_bound = 2 * self.discriminant.abs().bits_vartime().div_ceil(2);
    Self::reduce(log_2_a_bound, A, WideI::from(B), self.discriminant)
  }

  fn double(&self) -> CryptoBigintStackElement {
    let B_mu: I = self.b;

    // \gcd_1 when A_1 == A_2
    let g_1 = self.a;
    // \gcd_2
    let (e, u_2, v_2, _) = B_mu.abs().extended_gcd(g_1);
    let e = NonZero::new(e).unwrap();
    let A_div_e: U = self.a / e;
    let A: WideU = A_div_e.concatenating_mul(&A_div_e);

    let mod_1: U = A_div_e.overflowing_shl_vartime(1).unwrap();
    let two_A: WideU = A.overflowing_shl_vartime(1).unwrap();
    let mut mod_3 = two_A;

    let congruence_1 = self.b % mod_1;
    let e = e.get();

    // We drop the remainder here because `e` is explicitly a divisor of `B_mu`
    let B_mu_div_e = (B_mu / e).0;

    let wide_e = WideU::from((e, U::ZERO));
    let congruence_3 = {
      let congruence_3_rhs = {
        let congruence_3_rhs_numerator =
          -IStruct::from(*self.discriminant.abs() - self.b.abs().concatenating_square());
        let (congruence_3_rhs_mul_2, rem) = congruence_3_rhs_numerator / wide_e;
        debug_assert!(bool::from(rem.is_zero()));
        congruence_3_rhs_mul_2.half()
      } % mod_3;

      let congruence_3_lhs_factor = B_mu_div_e;

      /*
        We have `ax congruent to b mod c`.

        We can't scale `b` by `a**-1` as `a` may not have a multiplicative inverse `mod c`. We
        instead scale `a` by `u` where for `g = 1`, `a * u congruent to 1 mod c` (so `u` would be
        the multiplicative inverse of `a` if `g = 1`). When `g != 1`, this generalizes as
        `a * u congruent to g mod c`. Scaling `a` by `u` accordingly produces `a * a**-1 * g`,
        which we convert to `a * a**-1` via integer division by `g`.
      */

      // \gcd_3
      let g_is_2 = B_mu_div_e.abs().is_even();
      let g = <_>::ct_select(&WideU::ONE, &WideU::from(2u8), g_is_2);
      let mod_3_div_g =
        <_>::ct_select(&mod_3, &(mod_3.overflowing_shr_vartime(1).unwrap()), g_is_2);

      let u = {
        // u_3' = u_2 - u_2 |v_2| A_1/e
        let u_3_apo = IStruct::from(u_2).widen::<WideU>().widen::<WideWideU>() -
          IStruct::from(
            u_2.concatenating_mul(v_2.abs()).concatenating_mul(&Uint::from((A_div_e, Uint::ZERO))),
          );
        let u_3_apo = (u_3_apo % WideWideU::from((A, Uint::ZERO))).split().0;

        let u_3_target = <_>::ct_select(&(g % two_A), &Uint::ZERO, B_mu_div_e.abs().is_zero());

        #[cfg(debug_assertions)]
        {
          // u_3_apo is the multiplicative inverse of B_\mu / e % A_1**2/e**2
          debug_assert_eq!(
            u_3_apo.concatenating_mul(&Uint::from((B_mu_div_e.into_abs(), Uint::ZERO))) %
              Uint::from((A, Uint::ZERO)),
            <_>::ct_select(
              &(WideWideU::ONE % Uint::from((A, Uint::ZERO))),
              &Uint::ZERO,
              B_mu_div_e.abs().is_zero()
            )
          );
          // (u_3_apo << 1) * B_\mu / e % 2 * A_1**2/e**2 = 2
          debug_assert_eq!(
            (u_3_apo.overflowing_shl_vartime(1).unwrap())
              .concatenating_mul(&Uint::from((B_mu_div_e.into_abs(), Uint::ZERO))) %
              (Uint::from((two_A, Uint::ZERO))),
            <_>::ct_select(
              &(WideU::from(2u8) % (Uint::from((two_A, Uint::ZERO)))),
              &Uint::ZERO,
              B_mu_div_e.abs().is_zero()
            )
          );

          let u_3_g_is_1_target = <_>::ct_select(
            &(WideWideU::ONE % (Uint::from((two_A, Uint::ZERO)))),
            &Uint::ZERO,
            B_mu_div_e.abs().is_zero(),
          );

          // u_3_apo * B_\mu / e % 2 * A_1**2/e**2 \in {1, A_1**2/e**2 + 1}
          let is_one = (u_3_apo
            .concatenating_mul(&Uint::from((B_mu_div_e.into_abs(), Uint::ZERO))) %
            (Uint::from((two_A, Uint::ZERO))))
          .ct_eq(&u_3_g_is_1_target);
          let is_mod_plus_one = ((u_3_apo + A)
            .concatenating_mul(&Uint::from((B_mu_div_e.into_abs(), Uint::ZERO))) %
            (Uint::from((two_A, Uint::ZERO))))
          .ct_eq(&u_3_g_is_1_target);
          // In the case it's A_1**2/e**2 + 1, we only manage to clear it if B_\mu / e is odd
          // It will be odd if g is 1, so it is well-defined, but we want to ensure this check
          // passes (which it won't if `A_1**2/e**2 + 1` and B_\mu / e is even)
          debug_assert!(bool::from(B_mu_div_e.abs().is_even() | is_one | is_mod_plus_one));
        }

        let u_3 = <_>::ct_select(&u_3_apo, &(u_3_apo.overflowing_shl_vartime(1).unwrap()), g_is_2);
        let u_3_is_correct = (u_3
          .concatenating_mul(&Uint::from((B_mu_div_e.into_abs(), Uint::ZERO))) %
          (Uint::from((two_A, Uint::ZERO))))
        .ct_eq(&Uint::from((u_3_target, Uint::ZERO)));
        <_>::ct_select(&u_3, &(u_3 + A), !u_3_is_correct)
      };

      let res = congruence_3_rhs.concatenating_mul(&u);
      // Divide by `g`
      let res = <_>::ct_select(&res, &(res.overflowing_shr_vartime(1).unwrap()), g_is_2);
      mod_3 = mod_3_div_g;

      // Reduce res by the modulus
      let wide_mod_3 = WideWideU::from((mod_3, WideU::ZERO));
      let res = res % wide_mod_3;
      // Since this modulus only used the low bits, this only has low bits
      let res = res.split().0;
      <_>::ct_select(&(mod_3 - res), &res, congruence_3_lhs_factor.positive())
    };

    // \gcd_4 is omitted when A_1 == A_2

    let x = {
      // \gcd_5 when A_1 == A_2
      let (g, u, v) = {
        let mod_1 = Uint::from((mod_1, Uint::ZERO));
        let divisible_by_mod_1 = (mod_3 % mod_1).is_zero();
        let mod_1_div_2 = mod_1.overflowing_shr_vartime(1).unwrap();
        // If not divisible by `mod_1`, then twice `mod_3` is, meaning divisble by half `mod_1`
        // Since `mod_1, mod_2` are even, `mod_1` will be and half `mod_1` is well-defined
        let g = <_>::ct_select(&mod_1, &mod_1_div_2, !divisible_by_mod_1);

        // If `mod_3` is divisible by `mod_1`, then `u = 1, v = 0`
        let if_divisble_by_mod12 = (WideU::ONE, IStruct::from(WideU::ZERO));
        // If `mod_3` is greater than `mod_1` and divisible by `mod_1 / 2`, then
        // `u = mod_3.div_ceil(mod_1), v = -1`
        let if_gt_mod12_and_not_divisble_by_mod12 =
          ((mod_3 / mod_1) + WideU::ONE, -IStruct::from(WideU::ONE));
        // If `mod_3` is less than `mod_1` and divisible by `mod_1 / 2`, then
        // `mod_3 = mod_1 / 2`, and `u = 0, v = 1.
        let if_mod_3_eq_mod12_div_2 = (WideU::ZERO, IStruct::from(WideU::ONE));
        let mod_3_eq_mod12_div_2 = mod_3.ct_eq(&mod_1_div_2);

        let u = <_>::ct_select(
          &if_gt_mod12_and_not_divisble_by_mod12.0,
          &if_divisble_by_mod12.0,
          divisible_by_mod_1,
        );
        let u = <_>::ct_select(&u, &if_mod_3_eq_mod12_div_2.0, mod_3_eq_mod12_div_2);

        let v = <_>::ct_select(
          &if_gt_mod12_and_not_divisble_by_mod12.1,
          &if_divisble_by_mod12.1,
          divisible_by_mod_1,
        );
        let v = <_>::ct_select(&v, &if_mod_3_eq_mod12_div_2.1, mod_3_eq_mod12_div_2);

        (g, u, v)
      };

      const LIMBS: usize = crypto_bigint::nlimbs(BITS / 2);
      const TWICE_LIMBS: usize = crypto_bigint::nlimbs(BITS);
      const THRICE_LIMBS: usize = crypto_bigint::nlimbs(3 * (BITS / 2));
      const FIVE_LIMBS: usize = crypto_bigint::nlimbs(5 * (BITS / 2));

      let x1: IStruct<Uint<{ FIVE_LIMBS }>> =
        IStruct::<Uint<THRICE_LIMBS>>::from(mul_arbitrary_uints(congruence_1, mod_3)).mul_i_uint(v);
      let x2 = mul_arbitrary_uints::<THRICE_LIMBS, TWICE_LIMBS, FIVE_LIMBS>(
        mul_arbitrary_uints::<TWICE_LIMBS, LIMBS, THRICE_LIMBS>(congruence_3, mod_1),
        u,
      );
      let x = x1 + x2;

      let g_words = g.as_words();
      let mut wide_g = Uint::<{ FIVE_LIMBS }>::ZERO;
      wide_g.as_mut_words()[.. g_words.len()].copy_from_slice(g_words);
      let (x, rem) = x / wide_g;
      debug_assert!(bool::from(rem.is_zero()));

      x
    };

    let mut wide_two_A = Uint::<{ crypto_bigint::nlimbs(5 * (BITS / 2)) }>::ZERO;
    let two_A_words = two_A.as_words();
    wide_two_A.as_mut_words()[.. two_A_words.len()].copy_from_slice(two_A_words);
    let wide_B = x % wide_two_A;

    let mut B = WideU::ZERO;
    let wide_words_len = B.as_words().len();
    B.as_mut_words().copy_from_slice(&wide_B.as_words()[.. wide_words_len]);

    // Since `A = (A_1 / e) * (A_2 / e)`, where `e = gcd(A_1, A_2, B_mu)`, we assume `e = 1` and
    // the bound on `log_2(A)` becomes `log_2(A_1 * A_2)`
    let log_2_a_bound = 2 * self.discriminant.abs().bits_vartime().div_ceil(2);
    Self::reduce(log_2_a_bound, A, WideI::from(B), self.discriminant)
  }

  fn sub(&self, other: CryptoBigintStackElement) -> CryptoBigintStackElement {
    self.add(&-other)
  }

  fn multiexp(identity: &Self, pairs: &[(&Table<Self>, &[u8])]) -> Self {
    let mut longest_scalar_bits = 0;
    for (_table, scalar) in pairs {
      longest_scalar_bits = longest_scalar_bits.max(scalar.len() * 8);
    }

    let mut res: Option<Self> = None;
    for i in 0 .. longest_scalar_bits {
      // Shift over the existing result by a bit
      if let Some(res) = res.as_mut() {
        *res = res.double();
      }

      for (table, scalar) in pairs {
        let scalar_bits = scalar.len() * 8;
        // Transform the index of the bit in our longest scalar to the index of the bit in this one
        let Some(i) = i.checked_sub(longest_scalar_bits - scalar_bits) else {
          // If we're indexing a bit which doesn't exist in this scalar, continue
          continue;
        };

        // If it's time to add this entry, do so
        let table_bits = table.bits();
        if ((i + 1) % table_bits) == 0 {
          let mut accum = 0usize;
          debug_assert_eq!(i - (i + 1 - table_bits) + 1, table_bits);
          for i in (i + 1 - table_bits) ..= i {
            accum <<= 1;
            accum |= (usize::from(scalar[i / 8] >> (7 - (i % 8)))) & 1;
          }

          let mut to_add = Self::ct_select(&table[0], &table[1], 1.ct_eq(&accum));
          for i in 2 .. table.as_ref().len() {
            to_add = Self::ct_select(&to_add, &table[i], i.ct_eq(&accum));
          }
          res = Some(res.as_ref().map(|res| res.add(&to_add)).unwrap_or_else(|| to_add.clone()));
        }
      }
    }

    // Perform the final step of the accumulator
    for (table, scalar) in pairs {
      let scalar_bits = scalar.len() * 8;

      let table_bits = table.bits();
      let mut accum = 0usize;
      for i in ((scalar_bits / table_bits) * table_bits) .. scalar_bits {
        accum <<= 1;
        accum |= (usize::from(scalar[i / 8] >> (7 - (i % 8)))) & 1;
      }

      let mut to_add = Self::ct_select(&table[0], &table[1], 1.ct_eq(&accum));
      for i in 2 .. table.as_ref().len() {
        to_add = Self::ct_select(&to_add, &table[i], i.ct_eq(&accum));
      }
      res = Some(res.as_ref().map(|res| res.add(&to_add)).unwrap_or_else(|| to_add.clone()));
    }

    res.unwrap_or_else(|| identity.clone())
  }

  fn from_be_abc_discriminant_tess_root_unchecked(
    a: &[u8],
    b_positive: subtle::Choice,
    b: &[u8],
    _c: &[u8],
    abs_value_of_neg_discriminant: &[u8],
    _tess_root: &[u8],
  ) -> Self {
    if (8 * abs_value_of_neg_discriminant.len()) > usize::try_from(BITS - 128).unwrap() {
      panic!("too large of a discriminant");
    }

    let full_bytes = |bits: usize, bytes: &[u8]| {
      let mut full_bytes = vec![0u8; bits / 8];
      full_bytes[(bits / 8) - bytes.len() ..].copy_from_slice(bytes);
      full_bytes
    };

    let b = I::from(U::from_be_slice(&full_bytes(usize::try_from(A_BITS).unwrap(), b)));
    // TODO: ct_neg
    let b = I::ct_select(&-b, &b, b_positive.into());

    Self {
      a: U::from_be_slice(&full_bytes(usize::try_from(A_BITS).unwrap(), a)),
      b,
      discriminant: -WideI::from(WideU::from_be_slice(&full_bytes(
        usize::try_from(BITS).unwrap(),
        abs_value_of_neg_discriminant,
      ))),
    }
  }

  fn a(&self) -> Vec<u8> {
    let bytes = self.a.to_be_bytes();
    let mut start = 0;
    while bytes.get(start) == Some(&0) {
      start += 1;
    }
    bytes[start ..].to_vec()
  }

  fn b(&self) -> (subtle::Choice, Vec<u8>) {
    let bytes = self.b.abs().to_be_bytes();
    let mut start = 0;
    while bytes.get(start) == Some(&0) {
      start += 1;
    }
    (self.b.positive().into(), bytes[start ..].to_vec())
  }
}

impl Neg for CryptoBigintStackElement {
  type Output = Self;
  fn neg(self) -> Self {
    Self::reduce(
      self.discriminant.abs().bits_vartime().div_ceil(2),
      (&self.a).into(),
      (-self.b).widen(),
      self.discriminant,
    )
  }
}
