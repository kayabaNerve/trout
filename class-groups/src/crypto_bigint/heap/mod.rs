use core::ops::Neg;
use std::sync::Arc;

use zeroize::Zeroize;

use crypto_bigint::{CtEq, CtSelect, Resize, BoxedUint};

use crate::Table;

mod numbers;
use numbers::*;

/// A constant-time element of a class group, implemented via crypto-bigint's `BoxedUint`.
///
/// This is implemented in time variable to the discriminant yet constant to `a, b`. This prevents
/// timing analysis from leaking the elements being composed. It will work with a discriminant of
/// any size yet is only recommended for provers as it has a significant performance overhead to
/// other backends, which verifiers should take advantage of.
#[derive(Clone, Debug)]
pub struct CryptoBigintHeapElement {
  a: UnsignedInteger,
  b: Integer,
  discriminant: Arc<Integer>,
}

impl PartialEq for CryptoBigintHeapElement {
  fn eq(&self, other: &Self) -> bool {
    (self.a.ct_eq(&other.a) & self.b.ct_eq(&other.b) & self.discriminant.ct_eq(&other.discriminant))
      .into()
  }
}
impl Eq for CryptoBigintHeapElement {}

impl Zeroize for CryptoBigintHeapElement {
  fn zeroize(&mut self) {
    // Zeroize
    self.a.zeroize();
    self.b.zeroize();

    // Set to the identity
    self.a = UnsignedInteger::from(BoxedUint::one_with_precision(self.max_bits_for_a()));
    self.b =
      Integer::from(UnsignedInteger::from(BoxedUint::one_with_precision(self.max_bits_for_b())));
  }
}

impl crypto_bigint::CtSelect for CryptoBigintHeapElement {
  fn ct_select(&self, b: &Self, choice: crypto_bigint::Choice) -> Self {
    Self {
      a: UnsignedInteger::ct_select(&self.a, &b.a, choice),
      b: Integer::ct_select(&self.b, &b.b, choice),
      // Safe since `Element` is documented to have undefined behavior when mixed across class
      // groups
      discriminant: self.discriminant.clone(),
    }
  }
}

impl CryptoBigintHeapElement {
  fn max_bits_for_a(&self) -> u32 {
    // Lemma 5.3.4 of A Course in Computational Algebraic Number Theory
    self.discriminant.abs().0.bits_vartime().div_ceil(2) - 1
  }

  fn max_bits_for_b(&self) -> u32 {
    // For reduced elements, `|b| <= a`
    self.max_bits_for_a()
  }

  fn reduce(
    log_2_a_bound: u32,
    a: UnsignedInteger,
    b: Integer,
    discriminant: Arc<Integer>,
  ) -> Self {
    let mut b_decomposed = (b.positive(), b.into_abs().0);
    // Resize `a, b` to the size of the discriminant
    let a = a.0.resize(discriminant.abs().0.bits_precision());
    // Resize `b` to be the size of `a`
    b_decomposed.1 = b_decomposed.1.resize(discriminant.abs().0.bits_precision());
    let (a, mut b_decomposed, _c) =
      super::reduce(log_2_a_bound, a, b_decomposed, &discriminant.abs().0);
    // Resize `a` to equal length to the square root of the discriminant
    let a = a.resize(discriminant.abs().0.bits_vartime().div_ceil(2) + 1);
    // Resize `b` to the size of `a`
    b_decomposed.1 = b_decomposed.1.resize(discriminant.abs().0.bits_vartime().div_ceil(2) + 1);
    let b = Integer::from(UnsignedInteger::from(b_decomposed.1));
    Self { a: UnsignedInteger(a), b: <_>::ct_select(&-b.clone(), &b, b_decomposed.0), discriminant }
  }
}

impl crate::Element for CryptoBigintHeapElement {
  const MAX_TABLE_BITS: u32 = 8;

  fn is_identity(&self) -> subtle::Choice {
    (self.a.is_one() & self.b.positive() & self.b.abs().is_one()).into()
  }

  // Allegedly, Arndt's method, as specified on the Wikipedia page for binary quadratic forms
  fn add(&self, other: &Self) -> CryptoBigintHeapElement {
    let B_mu = (&self.b + &other.b).half();

    let e = self.a.gcd(&other.a).gcd(B_mu.abs());
    let (A1_div_e, _) = &self.a / &e;
    let (A2_div_e, _) = &other.a / &e;
    let A = &A1_div_e * &A2_div_e;

    let mod_1 = &A1_div_e << 1;
    let mod_2 = &A2_div_e << 1;
    let two_A = &A << 1;
    let mut mod_3 = two_A.clone();

    let congruence_1 = &self.b % &mod_1;
    let congruence_2 = &other.b % &mod_2;
    let congruence_3 = {
      let congruence_3_rhs = &{
        let congruence_3_rhs_numerator = &*self.discriminant + &(&self.b * &other.b);
        let (congruence_3_rhs_mul_2, rem) = &congruence_3_rhs_numerator / &e;
        debug_assert!(bool::from(rem.is_zero()));
        congruence_3_rhs_mul_2.half()
      } % &mod_3;

      // We drop the remainder here because `e` is explicitly a divisor of `B_mu`
      let congruence_3_lhs_factor = &(&B_mu / &e).0 % &mod_3;

      /*
        We have `ax congruent to b mod c`.

        We can't scale `b` by `a**-1` as `a` may not have a multiplicative inverse `mod c`. We
        instead scale `a` by `u` where for `g = 1`, `a * u congruent to 1 mod c` (so `u` would be
        the multiplicative inverse of `a` if `g = 1`). When `g != 1`, this generalizes as
        `a * u congruent to g mod c`. Scaling `a` by `u` accordingly produces `a * a**-1 * g`,
        which we convert to `a * a**-1` via integer division by `g`.
      */
      let (g, u) = congruence_3_lhs_factor.extended_gcd_part(&mod_3);
      let (res, rem) = &(&congruence_3_rhs * &u) / &g;
      debug_assert!(bool::from(rem.is_zero()));
      mod_3 = (&mod_3 / &g).0;
      &res % &mod_3
    };

    // CRT generalized for coprime moduli
    let crt = |congruence_1: &UnsignedInteger,
               mod_1: &UnsignedInteger,
               congruence_2: &UnsignedInteger,
               mod_2: &UnsignedInteger|
     -> (UnsignedInteger, UnsignedInteger) {
      let (g, u, v) = mod_1.extended_gcd(mod_2);
      debug_assert!(bool::from((congruence_1 % &g).ct_eq(&(congruence_2 % &g))));
      let M = &(mod_1 / &g).0 * mod_2;
      let x =
        &(&Integer::from(congruence_1 * mod_2) * &v) + &(&Integer::from(congruence_2 * mod_1) * &u);
      let (x, rem) = &x / &g;
      debug_assert!(bool::from(rem.0.is_zero()));
      debug_assert!(bool::from((&x % mod_1).ct_eq(congruence_1)));
      debug_assert!(bool::from((&x % mod_2).ct_eq(congruence_2)));
      (&x % &M, M)
    };

    let (congruence_12, mod_12) = crt(&congruence_1, &mod_1, &congruence_2, &mod_2);
    let (x, _mod_123) = crt(&congruence_12, &mod_12, &congruence_3, &mod_3);

    let B = &x % &two_A;

    debug_assert!(bool::from(congruence_1.ct_eq(&(&B % &mod_1))));
    debug_assert!(bool::from(congruence_2.ct_eq(&(&B % &mod_2))));
    debug_assert!(bool::from(congruence_3.ct_eq(&(&B % &mod_3))));

    let max_bits_for_a = self.max_bits_for_a();
    let log_2_a_1_bound = max_bits_for_a;
    let log_2_a_2_bound = max_bits_for_a;
    // Since `A = (A_1 / e) * (A_2 / e)`, where `e = gcd(A_1, A_2, B_mu)`, we assume `e = 1` and
    // the bound on `log_2(A)` becomes `log_2(A_1 * A_2)`
    let log_2_a_bound = log_2_a_1_bound + log_2_a_2_bound;
    Self::reduce(log_2_a_bound, A, Integer::from(B), self.discriminant.clone())
  }

  // A copy/paste of `Self::add` which removes the duplicated congruence for this specialization
  fn double(&self) -> CryptoBigintHeapElement {
    let B_mu = &self.b;

    let e = self.a.gcd(B_mu.abs());
    let (A_div_e, _) = &self.a / &e;
    let A = &A_div_e * &A_div_e;

    let mod_1 = &A_div_e << 1;
    let two_A = &A << 1;
    let mut mod_3 = two_A.clone();

    let congruence_1 = &self.b % &mod_1;
    let congruence_3 = {
      let congruence_3_rhs = &{
        let congruence_3_rhs_numerator = &*self.discriminant + &(&self.b * &self.b);
        let (congruence_3_rhs_mul_2, rem) = &congruence_3_rhs_numerator / &e;
        debug_assert!(bool::from(rem.is_zero()));
        congruence_3_rhs_mul_2.half()
      } % &mod_3;

      // We drop the remainder here because `e` is explicitly a divisor of `B_mu`
      let congruence_3_lhs_factor = &(B_mu / &e).0 % &mod_3;

      /*
        We have `ax congruent to b mod c`.

        We can't scale `b` by `a**-1` as `a` may not have a multiplicative inverse `mod c`. We
        instead scale `a` by `u` where for `g = 1`, `a * u congruent to 1 mod c` (so `u` would be
        the multiplicative inverse of `a` if `g = 1`). When `g != 1`, this generalizes as
        `a * u congruent to g mod c`. Scaling `a` by `u` accordingly produces `a * a**-1 * g`,
        which we convert to `a * a**-1` via integer division by `g`.
      */
      let (g, u) = congruence_3_lhs_factor.extended_gcd_part(&mod_3);
      let (res, rem) = &(&congruence_3_rhs * &u) / &g;
      debug_assert!(bool::from(rem.is_zero()));
      mod_3 = (&mod_3 / &g).0;
      &res % &mod_3
    };

    // CRT generalized for coprime moduli
    let crt = |congruence_1: &UnsignedInteger,
               mod_1: &UnsignedInteger,
               congruence_2: &UnsignedInteger,
               mod_2: &UnsignedInteger|
     -> (UnsignedInteger, UnsignedInteger) {
      let (g, u, v) = mod_1.extended_gcd(mod_2);
      debug_assert!(bool::from((congruence_1 % &g).ct_eq(&(congruence_2 % &g))));
      let M = &(mod_1 / &g).0 * mod_2;
      let x =
        &(&Integer::from(congruence_1 * mod_2) * &v) + &(&Integer::from(congruence_2 * mod_1) * &u);
      let (x, rem) = &x / &g;
      debug_assert!(bool::from(rem.0.is_zero()));
      debug_assert!(bool::from((&x % mod_1).ct_eq(congruence_1)));
      debug_assert!(bool::from((&x % mod_2).ct_eq(congruence_2)));
      (&x % &M, M)
    };

    let (x, _mod_123) = crt(&congruence_1, &mod_1, &congruence_3, &mod_3);

    let B = x;

    debug_assert!(bool::from(congruence_1.ct_eq(&(&B % &mod_1))));
    debug_assert!(bool::from(congruence_3.ct_eq(&(&B % &mod_3))));

    let max_bits_for_a = self.max_bits_for_a();
    let log_2_a_1_bound = max_bits_for_a;
    let log_2_a_2_bound = max_bits_for_a;
    let log_2_a_bound = log_2_a_1_bound + log_2_a_2_bound;
    Self::reduce(log_2_a_bound, A, Integer::from(B), self.discriminant.clone())
  }

  fn sub(&self, other: CryptoBigintHeapElement) -> CryptoBigintHeapElement {
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
    let b = Integer::from(UnsignedInteger::from_be_slice(b));
    // TODO: ct_neg
    let b = Integer::ct_select(&-b.clone(), &b, b_positive.into());

    let mut res = Self {
      a: UnsignedInteger::from_be_slice(a),
      b,
      discriminant: Arc::new(-Integer::from(UnsignedInteger::from_be_slice(
        abs_value_of_neg_discriminant,
      ))),
    };
    res.a.resize(res.max_bits_for_a());
    let max_bits_for_b = res.max_bits_for_b();
    res.b.abs_mut().resize(max_bits_for_b);
    res
  }

  fn a(&self) -> Vec<u8> {
    let mut bytes = self.a.to_be_bytes();
    while bytes.first() == Some(&0) {
      bytes.remove(0);
    }
    bytes
  }

  fn b(&self) -> (subtle::Choice, Vec<u8>) {
    let mut bytes = self.b.abs().to_be_bytes();
    while bytes.first() == Some(&0) {
      bytes.remove(0);
    }
    (self.b.positive().into(), bytes)
  }
}

impl Neg for CryptoBigintHeapElement {
  type Output = Self;
  fn neg(self) -> Self {
    Self::reduce(self.max_bits_for_a(), self.a, self.b.neg(), self.discriminant)
  }
}
