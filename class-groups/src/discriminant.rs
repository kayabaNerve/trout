//! Methods for sampling and working with discriminants (and the maps between them)
//!
//! We specifically provide the maps from
//! "A Cryptosystem Based on Non-maximal Imaginary Quadratic Orders with Fast Decryption" by
//! Detlef Hühnlein, Michael J. Jacobson, Jr., Sachar Paulus, and Tsuyoshi Takagi
//! (https://link.springer.com/content/pdf/10.1007/bfb0054134.pdf). These maps traditionally note
//! the prime conductor as `q`, yet the following consistently denote it as `p`. This is as
//! "Linearly Homomorphic Encryption from DDH" by Guilhem Castagnos and Fabien Laguillaumie
//! (https://eprint.iacr.org/2025/047) denote the prime conductor as `p` and we prefer consistency
//! with the latter paper.
//!
//! The two relevant maps from
//! "A Cryptosystem Based on Non-maximal Imaginary Quadratic Orders with Fast Decryption" require
//! a `FindIdealPrimeTo` function. We specify it here as a `coprime_from` function, specified
//!/ as follows:
//!
//! ```py
//! fn coprime_form(a, b, c, p) {
//!   if gcd(a, p) == 1 {
//!     return (a, b)
//!   }
//!   if gcd(c, p) == 1 {
//!     return (c, -b)
//!   }
//!   return (c + (b + a), -(b + (2 * a)))
//! }
//! ````
//!
//! Our function has the same bounds on the input, that the form is primitive, and achieves the
//! same bounds on the output, that the `a` coefficient is coprime to the prime `p`. Note we do
//! input the `c` coefficient in order to calculate the result yet yield the result without its `c`
//! coefficient. If necessary, it can be calculated via the yielded `a, b` coefficients and the
//! corresponding discriminant, as usual.
//!
//! For correctness, it should be noted there are three cases:
//!
//! 1) If `gcd(a, p) == 1`, the output is the input
//! 2) Else if `gcd(c, p) == 1`, we apply the transformation `(a, b, c)` -> `(c, -b, a)`
//! 3) Else, we apply the transformation `(a, b, c)` -> `(a, b + 2 a, c + b + a)` followed by the
//!    transformation `(a, b, c)` -> `(c, -b, a)`. This is a special case of the general
//!    transformation, `(a, b + 2 m a, c + m b + m^2 a)`, with `m = 1`.
//!
//! Having established the form is equivalent, we are left to argue the resulting `a` coefficient
//! is coprime to `p`. This is a result of `p` being prime and the form being primitive such that
//! `gcd(a, b, c) = 1`. Accordingly, either `a`, `b`, or `c` must be coprime to `q`, as if all
//! weren't, we'd have the contradiction `gcd(a, b, c) = q`. If `a` is coprime, the form is left
//! as-is. If `c` is coprime, we return the equivalent (unreduced) form where the new `a`
//! coefficient is the old `c` coefficient. Finally, if neither `a` nor `c` are coprime, we know
//! their sum `a + c` is a multiple of `q` and `b` must be coprime to `q`. Accordingly,
//! `(a + c) + b` will be coprime to `q`, hence why we return an equivalent form with that as the
//! `a` coefficient. We do specify this as `c + (b + a)`, which is equivalent, as we are able to
//! bound `b + a` as being positive for reduced positive definite forms, simplifying the bounds on
//! that intermediary term.

use rand::CryptoRng;
use ::crypto_bigint::{
  Choice, CtOption, CtEq, CtSelect, Zero, One, NonZero, Odd, Limb, Mul, Div, Gcd, NegMod,
  InvertMod, BitOps, Encoding,
};

use crate::Element;

/// For a primitive reduced positive definite form of negative discriminant, return the
/// equivalent form whose `a` coefficient is coprime to the prime `p`.
///
/// The inputs MUST have sufficient capacity to calculate `a + b + c, b + 2 a`. Additionally,
/// `a, b, c, p` MUST be of the same size.
///
/// This function runs in constant time. It WILL NOT return `None` if the inputs are satisfied but
/// MAY return `None` if for invalid inputs, if it fails to find an equivalent form with a coprime
/// `a` coefficient.
#[must_use]
fn coprime_form<P, U: AsRef<[Limb]> + AsMut<[Limb]> + CtSelect + Gcd<P, Output: One>>(
  mut a: U,
  (mut b_positive, mut b_abs): (Choice, U),
  mut c: U,
  p: &P,
) -> CtOption<(U, (Choice, U))> {
  let a_is_coprime = a.gcd(p).is_one();
  let c_is_coprime = c.gcd(p).is_one();

  // If neither are coprime, map with `m = 1`
  let neither_a_c_coprime = !(a_is_coprime | c_is_coprime);
  let mut correct = Choice::TRUE;
  {
    // We start by calculating `b + a`, stored to where `b` is, negating `b` if necessary
    {
      let mut carry = Limb::from(u8::from(!b_positive));
      let mask = Limb::ZERO.wrapping_sub(carry);
      for (b_limb, a_limb) in b_abs.as_mut().iter_mut().zip(a.as_ref()) {
        let new_limb;
        (new_limb, carry) = ((*b_limb) ^ mask).carrying_add(*a_limb, carry);
        *b_limb = Limb::ct_select(b_limb, &new_limb, neither_a_c_coprime);
      }
      /*
        We require either:
        - No change was applied
        - `b` was negative, as the difference of two numbers of equivalent capacity always fits
          within the capacity of one said numbers
        - `carry` is zero (this did not overflow)
      */
      correct &= (!neither_a_c_coprime) | (!b_positive) | carry.is_zero();
      // $0 \le b + a$, so if we just calculated `b + a`, this is positive
      b_positive |= neither_a_c_coprime;
    }

    // We now sum `b + a` into `c` and update `b + a` to `b + 2a` to complete the map with `m = 1`
    {
      let mut c_carry = Limb::ZERO;
      let mut b_carry = Limb::ZERO;
      for ((a_limb, b_limb), c_limb) in a.as_ref().iter().zip(b_abs.as_mut()).zip(c.as_mut()) {
        let new_c_limb;
        (new_c_limb, c_carry) =
          c_limb.carrying_add(Limb::ct_select(&Limb::ZERO, b_limb, neither_a_c_coprime), c_carry);
        *c_limb = new_c_limb;

        let new_b_limb;
        (new_b_limb, b_carry) =
          b_limb.carrying_add(Limb::ct_select(&Limb::ZERO, a_limb, neither_a_c_coprime), b_carry);
        *b_limb = new_b_limb;
      }
      correct &= c_carry.is_zero() & b_carry.is_zero();
    }
  }

  // If `a` was not coprime, perform the swap with `c` (necessary when `c` was coprime or `b` was)
  {
    let swap = !a_is_coprime;
    U::ct_swap(&mut a, &mut c, swap);
    b_positive ^= swap;
  }

  correct &= a.gcd(p).is_one();
  CtOption::new((a, (b_positive, b_abs)), correct)
}

/// Check if two little-endian encodings represent the same number.
///
/// This function runs in time independent to the encoded values and is considered to run in
/// constant time, though it is in time variable to the lengths of the inputs (which are not
/// considered secrets).
///
/// This function does not check the encodings are canonical and does allow trailing zero bytes.
fn le_malleable_eq(a: &[u8], b: &[u8]) -> Choice {
  let mut eq = Choice::TRUE;

  // Check mutually present bytes for equality
  let mutual_len = a.len().min(b.len());
  for (a, b) in a[.. mutual_len].iter().zip(&b[.. mutual_len]) {
    eq &= a.ct_eq(b);
  }

  // Check non-mutual bytes are zero
  for a in &a[mutual_len ..] {
    eq &= a.ct_eq(&0);
  }
  for b in &b[mutual_len ..] {
    eq &= b.ct_eq(&0);
  }

  eq
}

/// A discriminant of a class group.
pub trait Discriminant {}
/// A negative discriminant of a class group.
pub trait NegativeDiscriminant: Discriminant {
  /// An upper bound on the order of the class group with this discriminant.
  ///
  /// This function runs in variable time. This MAY panic if this discriminant is ill-defined or
  /// absurdly large. This returns `k` such that $2^k$ is greater than or equal to the order (class
  /// number) of this group.
  fn upper_bound_on_order(&self) -> u32 {
    /*
      Per Section 5.10.1 of A Course in Computational Algebraic Number Theory by Henri Cohen, for
      all discriminants less than `-4`, an upper bound on the class number is
      $ln(|D|) sqrt(|D|) / \pi$. We simplify this to
      $2^{\lceil log_2(log_2(|D|) sqrt(|D|) / 2) \rceil}$.

      `-1, -2` are not congruent to `0` nor `1` modulo `4`, as required to be a discriminant of a
      class group. `-3, -4` both have the class number `1` and are therefore satisfied by any
      output we return (as $0$ is the smallest possible result and $2^0$ is greater than or equal
      to the class number of discriminants `-3, -4`).

      This means the following is complete for all negative discriminants.
    */
    let absolute_value = self.absolute_value();
    let mut absolute_value = absolute_value.as_ref();
    while absolute_value.last() == Some(&0) {
      absolute_value = &absolute_value[.. (absolute_value.len() - 1)];
    }
    let discriminant_bits = u32::try_from(8 * absolute_value.len()).expect("4 GB discriminant?") -
      absolute_value
        .last()
        .expect("negative discriminant's absolute value was zero")
        .leading_zeros();
    let sqrt_bits = discriminant_bits.div_ceil(2);
    let logarithm_bits = discriminant_bits.ilog2() + 1;
    logarithm_bits + sqrt_bits - 1
  }

  /// The absolute value of this discriminant.
  ///
  /// This is returned as its little-endian encoding.
  fn absolute_value(&self) -> impl AsRef<[u8]>;
}
/// An odd discriminant.
pub trait OddDiscriminant: Discriminant {}
/// A fundamental (square-free) discriminant.
pub trait FundamentalDiscriminant: Discriminant {
  /// Take an element of the class group with fundamental discriminant and apply the injection such
  /// that it is mapped to an element of the class group with non-fundamental discriminant.
  ///
  /// This implements Algorithm 2, `GoToNonMaxOrder`. We specify it as follows for primitive forms
  /// of fundamental negative discriminants:
  ///
  /// ```py
  /// fn inject(a, b, c, p) {
  ///   discriminant = (b * b) - (4 * a * c)
  ///   (a, b) = coprime_form(a, b, c, p)
  ///   return reduce(a, b * p, discriminant * p * p)
  /// }
  /// ```
  ///
  /// This is slightly different in that we do not specify the reduction of $b \mod 2 a$. Instead,
  /// we assume the existence of a reduction function, `reduce`, which inputs the `a, b`
  /// coefficients of an unreduced form and its discriminant before yielding a reduced form.
  ///
  /// The resulting form is primitive however. First, the input is bound to be primitive. Second,
  /// `coprime_form` yields an equivalent form, where equivalence preserves primitivity. Finally,
  /// `coprime_form` yields a form whose `a` coefficient is coprime to `p`, so scaling the `b`
  /// coefficient by `p` won't affect the greatest common divisor of `a, b`.
  ///
  /// This function MAY panic or return an incorrect result if `element` is not of this
  /// discriminant. This function runs in time only variable to the discriminant, the length of the
  /// encoding of `p`, and `E::a_b_c_discriminant` (which may be implemented in constant-time).
  #[cfg(feature = "alloc")] // TODO no-`alloc`
  fn inject<E: Element>(&self, element: impl Element, p: &impl Encoding) -> E
  where
    Self: NegativeDiscriminant,
  {
    use crypto_bigint::{ConcatenatingMul, ConcatenatingSquare, Resize, BoxedUint};

    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b_abs), c, discriminant_abs) = unsafe { element.a_b_c_discriminant() };
    assert!(bool::from(le_malleable_eq(self.absolute_value().as_ref(), discriminant_abs.as_ref())));

    // This is only vartime with regards to the length of the encoding
    let a = BoxedUint::from_le_slice_vartime(a.as_ref());
    let b_abs = BoxedUint::from_le_slice_vartime(b_abs.as_ref());
    let c = BoxedUint::from_le_slice_vartime(c.as_ref());

    let discriminant_abs = BoxedUint::from_le_slice_vartime(discriminant_abs.as_ref());
    let p = {
      let p = p.to_le_bytes();
      BoxedUint::from_le_slice_vartime(p.as_ref())
    };

    let discriminant_abs = discriminant_abs.concatenating_mul(p.concatenating_square());

    let bits_precision = 2 + a.bits_precision().max(b_abs.bits_precision()).max(c.bits_precision());
    let p = p.resize(bits_precision);
    let (a, (b_positive, b_abs)) = coprime_form(
      a.resize(bits_precision),
      (b_positive, b_abs.resize(bits_precision)),
      c.resize(bits_precision),
      &p,
    )
    .expect("could not find a coprime form (non-primitive or unreduced?)");

    let b_abs = b_abs.concatenating_mul(&p);

    // TODO: Tighten this
    let log_2_bound = 8 + bits_precision.max(discriminant_abs.bits_precision());
    let discriminant_abs = discriminant_abs.resize(log_2_bound);
    /*
      The form is valid. The numbers are within `log_2_bound`. The numbers are the same size, and
      with a spare bit of capacity. This causes our call to `partial_reduce` to be valid.
    */
    let (a, (b_positive, b_abs), c) = crate::crypto_bigint::partial_reduce(
      log_2_bound,
      a.resize(log_2_bound),
      (b_positive, b_abs.resize(log_2_bound)),
      &discriminant_abs,
    );
    /*
      As correct for `partial_reduce`, we are correct for `reduce`. We do tighten our bound to the
      square root of the discriminant, but this is a bound on the output from `partial_reduce`.
    */
    let discriminant_bits = discriminant_abs.bits_vartime();
    let sqrt_discriminant_bits = discriminant_bits.div_ceil(2);
    let (a, (b_positive, b_abs), c) =
      crate::crypto_bigint::reduce(sqrt_discriminant_bits, a, (b_positive, b_abs), c);

    /*
      SAFETY:

      This form is well-defined. For $b^2 - 4 a c = -|delta|$, we want to assert
      $(b p)^2 - 4 a c' = -|delta| p^2$ has a solution for `c'` when given arbitrary `p`.

      $b b p p + |delta| p p = 4 a c'$
      $(b b + |delta|) p p = 4 a c'$

      $4 a$ is a divisor of $b b + |delta|$ and therefore there is a solution for $c'$.

      This form is primitive as the input was primitive, and while `b` now has a `p` factor, `p` is
      coprime to `a`. Additionally, the reduction preserves primitivity.

      This form is reduced as we've explicitly reduced it.
    */
    let discriminant_bits = usize::try_from(discriminant_bits).unwrap();
    let sqrt_discriminant_bits = usize::try_from(sqrt_discriminant_bits).unwrap();
    unsafe {
      E::from_coefficients(
        &a.to_le_bytes().as_ref()[.. sqrt_discriminant_bits.div_ceil(8)],
        (b_positive, &b_abs.to_le_bytes().as_ref()[.. sqrt_discriminant_bits.div_ceil(8)]),
        &c.to_le_bytes()[.. discriminant_bits.div_ceil(8)],
        &discriminant_abs.to_le_bytes()[.. discriminant_bits.div_ceil(8)],
      )
    }
  }
}

/// A fundamental discriminant as part of the CL15 cryptosystem.
///
/// This is constructed as detailed in "Linearly Homomorphic Encryption from DDH" by
/// Guilhem Castagnos and Fabien Laguillaumie (https://eprint.iacr.org/2025/047), corresponding to
/// $\Delta_K$.
///
/// `Up` is the numeric type used to represent the prime `p`. `Udk` is the numeric type used to
/// represent the discriminant's absolute value, the product $q * p$.
#[derive(Clone)]
pub struct Cl15k<Up, Udk> {
  p: Odd<Up>,
  absolute_value: Udk,
}
impl<Up, Udk> Discriminant for Cl15k<Up, Udk> {}
impl<Up, Udk: Encoding> NegativeDiscriminant for Cl15k<Up, Udk> {
  fn absolute_value(&self) -> impl AsRef<[u8]> {
    self.absolute_value.to_le_bytes()
  }
}
impl<Up, Udk> OddDiscriminant for Cl15k<Up, Udk> {}
impl<Up, Udk> FundamentalDiscriminant for Cl15k<Up, Udk> {}

impl<Up, Udk> Cl15k<Up, Udk> {
  /// The prime `p` from the setup.
  pub fn p(&self) -> &Up {
    &self.p
  }
}

/// A non-fundamental discriminant as part of the CL15 cryptosystem.
///
/// This is constructed as detailed in Linearly Homomorphic Encryption from DDH by
/// Guilhem Castagnos and Fabien Laguillaumie (https://eprint.iacr.org/2025/047), correspond to
/// $\Delta_p$.
///
/// `Up` is the numeric type used to represent the prime `p`. `Udk` is the numeric type used to
/// represent the fundamental discriminant's absolute value, the product $q * p$. `Udp` is the
/// numeric type used to represent the non-fundamental discriminant's absolute value, the product
/// $q * p^3$.
#[derive(Clone)]
pub struct Cl15p<Up, Up2, Udk, Udp> {
  fundamental: Cl15k<Up, Udk>,
  p_square: Odd<Up2>,
  absolute_value: Udp,
}
impl<Up, Up2, Udk, Udp> Discriminant for Cl15p<Up, Up2, Udk, Udp> {}
impl<Up: BitOps, Up2, Udk: Encoding, Udp: Encoding> NegativeDiscriminant
  for Cl15p<Up, Up2, Udk, Udp>
{
  /// This runs in variable time to this discriminant.
  fn upper_bound_on_order(&self) -> u32 {
    /*
      B.1 of Linearly Homomorphic Encryption from DDH establishes the order of this discriminant is
      equal to the order of the fundamental discriminant multiplied by `p` if the fundamental
      discriminant is less than `4`. As $q > 4 p$, no fundamental discriminant within the CL15
      cryptosystem will be greater than or equal to `-4`.

      While this bound can be relaxed, as discussed in Section 4.1, we do not implement or support
      that extension of the scheme.
    */
    self.fundamental.upper_bound_on_order() + self.fundamental.p.as_ref().bits_vartime()
  }

  fn absolute_value(&self) -> impl AsRef<[u8]> {
    self.absolute_value.to_le_bytes()
  }
}
impl<Up, Up2, Udk, Udp> OddDiscriminant for Cl15p<Up, Up2, Udk, Udp> {}

// TODO: Properly generic
impl
  Cl15p<
    crypto_bigint::BoxedUint,
    crypto_bigint::BoxedUint,
    crypto_bigint::BoxedUint,
    crypto_bigint::BoxedUint,
  >
{
  /// Sample a fundamental discriminant as described by the CL15 cryptosystem.
  // TODO: Result
  pub fn sample(
    mut rng: impl CryptoRng,
    lambda: u64,
    p_le_bytes: impl AsRef<[u8]>,
  ) -> Option<Self> {
    // TODO: Remove malachite
    use ::malachite::{
      base::num::{arithmetic::traits::*, logic::traits::*},
      *,
    };
    use crate::malachite::{natural_from_bytes, natural_to_bytes};
    use crypto_bigint::BoxedUint;

    let p = natural_from_bytes(p_le_bytes.as_ref());

    let mu = p.significant_bits();

    // Step 1
    if lambda < (mu + 2) {
      None?;
    }

    // Step 2
    let q = {
      let q_bits = (2 * lambda) - mu;
      let q_bits = u32::try_from(q_bits).unwrap();
      loop {
        let mut seed = vec![0; usize::try_from(q_bits).unwrap().div_ceil(8)];
        rng.fill_bytes(&mut seed);
        if (q_bits % 8) != 0 {
          let high_bit = 1 << ((q_bits % 8) - 1);
          // Ensure the high bit is set
          seed[0] |= high_bit;
          // Mask off any higher bits
          seed[0] &= (high_bit << 1) - 1;
        }
        let q = super::primes::next_prime(
          &mut rng,
          seed,
          ({
            let kappa = u32::try_from((8 * p_le_bytes.as_ref().len()) / 2).unwrap();
            let mut closest_power_of_two = 1u32;
            while (2 * closest_power_of_two) < kappa {
              closest_power_of_two <<= 1;
            }

            // $closest_power_of_two < kappa \le (2 * closest_power_of_two)$
            if kappa.abs_diff(closest_power_of_two) >= kappa.abs_diff(closest_power_of_two << 1) {
              closest_power_of_two <<= 1;
            }
            closest_power_of_two
          })
          .max(128),
        );
        let q = natural_from_bytes(q.to_le_bytes().as_ref());
        debug_assert!((q.significant_bits() - u64::from(q_bits)) < 1);
        // p * q is congruent to -1 mod 4
        if ((&p * &q) & Natural::from(3u8)) != 3u8 {
          continue;
        }
        // jacobi of p/q = -1
        let res = p.clone().jacobi_symbol(&q);
        if res != -1 {
          continue;
        }
        break q;
      }
    };

    // Step 3
    let delta_k = -Integer::from(&p * &q);

    let p_square = p.clone().pow(2u64);
    let delta_p = &delta_k * Integer::from(p_square.clone());

    Some(Cl15p {
      fundamental: Cl15k {
        p: Odd::new(BoxedUint::from_le_slice_vartime(&natural_to_bytes(&p))).unwrap(),
        absolute_value: BoxedUint::from_le_slice_vartime(&natural_to_bytes(
          delta_k.unsigned_abs_ref(),
        )),
      },
      p_square: Odd::new(BoxedUint::from_le_slice_vartime(&natural_to_bytes(&p_square))).unwrap(),
      absolute_value: BoxedUint::from_le_slice_vartime(&natural_to_bytes(
        delta_p.unsigned_abs_ref(),
      )),
    })
  }
}

impl<Up, Up2, Udk, Udp> Cl15p<Up, Up2, Udk, Udp> {
  /// The fundamental discriminant.
  pub fn fundamental_discriminant(&self) -> &Cl15k<Up, Udk> {
    &self.fundamental
  }
}

impl<Up: Encoding, Up2: Encoding, Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding>
  Cl15p<Up, Up2, Udk, Udp>
{
  /// The element of `p`-order with an easy discrete-log problem.
  pub fn f<E: Element>(&self) -> E {
    // $b^2 + |delta| = p^2 + (q p p^2) = (q p + 1) p^2 = 4 a c$
    // $a = p^2$ so $c = (q p + 1) / 4$
    let c = {
      // `q p`
      let mut c = self.fundamental.absolute_value.clone();
      {
        let c = <_ as AsMut<[Limb]>>::as_mut(&mut c);
        // `q p` -> `q p + 1`
        let mut carry = Limb::ONE;
        for c_limb in c.iter_mut() {
          let new_limb;
          (new_limb, carry) = c_limb.carrying_add(Limb::ZERO, carry);
          *c_limb = new_limb;
        }
        // Shift right by two to divide by four
        carry <<= Limb::BITS - 2;
        for c_limb in c.iter_mut().rev() {
          let new_limb = carry | ((*c_limb) >> 2);
          carry = (*c_limb) << (Limb::BITS - 2);
          *c_limb = new_limb;
        }
        debug_assert!(bool::from(carry.is_zero()));
      }
      c
    };

    /*
      SAFETY:

      This form is well-defined, as we defined (and calculated) the satisfactory `c` coefficient
      above.

      This form is primitive (TODO).

      This form is reduced as $|b| < a, b \ne a$ and $a < sqrt(|delta| / 4)$. For the latter claim,
      we require $q > 4 p$ during our setup, where this discriminant is of form $q p^3$. Therefore,
      $p^2 < sqrt(|delta| / 4)$.
    */
    unsafe {
      E::from_coefficients(
        self.p_square.to_le_bytes(),
        (Choice::TRUE, self.fundamental.p.to_le_bytes()),
        c.to_le_bytes(),
        self.absolute_value.to_le_bytes(),
      )
    }
  }
}

impl<Up: BitOps + Encoding, Up2, Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding>
  Cl15p<Up, Up2, Udk, Udp>
{
  /// Take an element of the class group with non-fundamental discriminant and apply the surjection
  /// such that it is mapped to an element of the class group with fundamental discriminant.
  ///
  /// This implements Algorithm 3, `GoToMaxOrder`. We specify it as follows for primitive forms
  /// of negative discriminants where `discriminant / (p * p)` is fundamental:
  ///
  /// ```py
  /// fn surject(a, b, c, p) {
  ///   discriminant = (b * b) - (4 * a * c)
  ///   fundamental_discriminant = discriminant / (p * p)
  ///   assert (fundamental_discriminant * p * p) == discriminant
  ///   (a, b) = coprime_form(a, b, c, p)
  ///   (mu, lambda, _one) = xgcd(p, a)
  ///   return reduce(
  ///     a,
  ///     (b * mu) + (a * (fundamental_discriminant % 2) * lambda),
  ///     discriminant / (p * p)
  ///   )
  /// }
  /// ```
  ///
  /// As with [`FundamentalDiscriminant::inject`], we do not specify the reduction of $b \mod 2 a$.
  /// Instead, we again assume the existence of a reduction function, `reduce`, which inputs the
  /// `a, b` coefficients of an unreduced form and its discriminant before yielding a reduced form.
  /// We also assume an `xgcd` function, which for `xgcd(x, y)`, returns `(u, v, d)` such that
  /// `u x + v y = d`.
  ///
  /// This function MAY panic or return an incorrect result if `element` is not of this
  /// discriminant. This function runs in time only variable to this discriminant and
  /// `E::a_b_c_discriminant` (which may or may not be implemented in constant-time).
  #[cfg(feature = "alloc")] // TODO: no-`alloc`
  pub fn surject<E: Element>(&self, element: impl Element) -> E {
    use crypto_bigint::{CtGt, ConcatenatingMul, Resize, BoxedUint};

    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b_abs), c, discriminant_abs) = unsafe { element.a_b_c_discriminant() };
    assert!(bool::from(le_malleable_eq(self.absolute_value().as_ref(), discriminant_abs.as_ref())));

    // This is only vartime with regards to the length of the encoding
    let a = BoxedUint::from_le_slice_vartime(a.as_ref());
    let b_abs = BoxedUint::from_le_slice_vartime(b_abs.as_ref());
    let c = BoxedUint::from_le_slice_vartime(c.as_ref());
    let p = self.fundamental.p.to_le_bytes();
    let p = BoxedUint::from_le_slice_vartime(p.as_ref());

    let bits_precision = 2 + a.bits_precision().max(b_abs.bits_precision()).max(c.bits_precision());
    let p = p.resize(bits_precision);
    let (a, (mut b_positive, b_abs)) = coprime_form(
      a.resize(bits_precision),
      (b_positive, b_abs.resize(bits_precision)),
      c.resize(bits_precision),
      &p,
    )
    .expect("could not find a coprime form (non-primitive or unreduced?)");

    /*
      We calculate our new `b` coefficient modulo `2 a`, which represents an equivalent form.

      We do not consider the `fundamental_discriminant % 2` term as we know the fundamental
      discriminant to be odd, and therefore the term to be equal to `1`, which is the identity (as
      it's used in a multiplication).

      We do not calculate `a * lambda` but solely `a * (lambda & 1)`, as we know `a` generates a
      2-subgroup of `2 a` with addition. However, as we have `(mu * p) - 1 = lambda * a`, we also
      know that the trailing zero bits in `(mu * p) - 1` is equal to the trailing zero bits in
      `lambda * a`. This lets us determine `(lambda & 1) == 0` as
      `trailing_zeroes((mu * p) - 1) > trailing_zeroes(a)`.
    */
    let b_abs = {
      let a = NonZero::new(a.clone())
        .expect("`a` is non-zero for a positive definite form of negative discriminant");
      let mu = p.invert_mod(&a).expect("`a` is coprime to `p`");
      let lambda_is_even =
        (mu.concatenating_mul(&p) - BoxedUint::one()).trailing_zeros().ct_gt(&a.trailing_zeros());

      let a = a.get();
      let two_a = NonZero::new(a.clone().concatenating_add(&a))
        .expect("`2 a` is non-zero as `a` is non-zero");

      let b_mu = b_abs.mul_mod(&mu, &two_a);
      let b_mu = <_>::ct_select(&b_mu.clone().neg_mod(&two_a), &b_mu, b_positive);
      b_positive = Choice::TRUE;

      // This is a subtraction as the `lambda` coefficient is negative
      b_mu.sub_mod(
        &<_>::ct_select(&BoxedUint::zero_like(&a), &a, !lambda_is_even)
          .resize(b_mu.bits_precision()),
        &two_a,
      )
    };

    let discriminant_abs =
      BoxedUint::from_le_slice_vartime(self.fundamental_discriminant().absolute_value().as_ref());

    // TODO: Tighten this
    let log_2_bound =
      8 + bits_precision.max(b_abs.bits_precision()).max(discriminant_abs.bits_precision());
    let discriminant_abs = discriminant_abs.resize(log_2_bound);
    /*
      The form is valid. The numbers are within `log_2_bound`. The numbers are the same size, and
      with a spare bit of capacity. This causes our call to `partial_reduce` to be valid.
    */
    let (a, (b_positive, b_abs), c) = crate::crypto_bigint::partial_reduce(
      log_2_bound,
      a.resize(log_2_bound),
      (b_positive, b_abs.resize(log_2_bound)),
      &discriminant_abs,
    );
    /*
      As correct for `partial_reduce`, we are correct for `reduce`. We do tighten our bound to the
      square root of the discriminant, but this is a bound on the output from `partial_reduce`.
    */
    let discriminant_bits = discriminant_abs.bits_vartime();
    let sqrt_discriminant_bits = discriminant_bits.div_ceil(2);
    let (a, (b_positive, b_abs), c) =
      crate::crypto_bigint::reduce(sqrt_discriminant_bits, a, (b_positive, b_abs), c);

    /*
      SAFETY:
      - This form is well-defined (TODO).
      - This form is primitive (TODO).
      - This form is reduced as we've explicitly reduced it.
    */
    let discriminant_bits = usize::try_from(discriminant_bits).unwrap();
    let sqrt_discriminant_bits = usize::try_from(sqrt_discriminant_bits).unwrap();
    unsafe {
      E::from_coefficients(
        &a.to_le_bytes().as_ref()[.. sqrt_discriminant_bits.div_ceil(8)],
        (b_positive, &b_abs.to_le_bytes().as_ref()[.. sqrt_discriminant_bits.div_ceil(8)]),
        &c.to_le_bytes()[.. discriminant_bits.div_ceil(8)],
        &discriminant_abs.to_le_bytes()[.. discriminant_bits.div_ceil(8)],
      )
    }
  }

  /// Apply the coset labeling function to an element of this discriminant.
  ///
  /// This is equivalent to the following:
  ///
  /// ```py
  /// fn coset_labeling_function(a, b, c, p) {
  ///   return inject(surject(a, b, c, p), p)
  /// }
  /// ```
  ///
  /// This function MAY panic or return an incorrect result if `element` is not of this
  /// discriminant. This function runs in time only variable to this discriminant and
  /// `E::a_b_c_discriminant` (which may or may not be implemented in constant-time).
  #[cfg(feature = "alloc")] // TODO: no-`alloc`
  pub fn coset_labeling_function<E: Element>(&self, element: impl Element) -> E {
    self.fundamental_discriminant().inject(self.surject::<E>(element), self.fundamental.p.as_ref())
  }
}

impl<
  Up: Clone + CtSelect + Zero + NegMod<Output = Up> + InvertMod<Output = Up> + BitOps + Encoding,
  Up2: Encoding,
  Udk,
  Udp: Clone
    + CtEq
    + for<'a> Mul<&'a Up, Output = Udp>
    + for<'a> Div<&'a NonZero<Up>, Output = Udp>
    + Encoding,
> Cl15p<Up, Up2, Udk, Udp>
{
  /// Solve for the discrete logarithm of an element of order-`p`.
  ///
  /// We specify this as follows, for a reduced form's `a, b` coefficients and the prime `p`:
  ///
  /// ```py
  /// fn discrete_logarithm(a, b, p) {
  ///   if (a, b) == (1, 1) {
  ///     return 0
  ///   }
  ///   assert a == p^2
  ///   x_tilde = (b / p)
  ///   assert (x_tilde * p) == b
  ///   (u, _v, _one) = xgcd(x_tilde, p)
  ///   return u
  /// }
  /// ```
  ///
  /// The `if` is used to check if the element is identity and therefore has a discrete-logarithm
  /// of `0`. Else, we apply the defined methodology of `Solve` (presented in Figure 2) from
  /// Linearly Homomorphic Encryption from DDH by Guilhem Castagnos and Fabien Laguillaumie
  /// (https://eprint.iacr.org/2025/047). We explicitly specify the calculation of
  /// $\tilde{x}^{-1} \mod p$ via `xgcd(x_tilde, p)` as we've already assumed the existence of an
  /// `xgcd` function elsewhere in our specification, though other methods would work as well and
  /// MAY be used instead (such as by Fermat's Little Theorem or a Bernstein-Yang inversion).
  ///
  /// This function runs time only variable to this discriminant and `E::a_b_c_discriminant` (which
  /// may or may not be implemented in constant-time).
  pub fn discrete_logarithm(&self, element: impl Element) -> CtOption<Up> {
    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b_abs), _c, discriminant_abs) = unsafe { element.a_b_c_discriminant() };

    let correct_discriminant =
      le_malleable_eq(self.absolute_value.to_le_bytes().as_ref(), discriminant_abs.as_ref());
    let correct_a_coefficient =
      le_malleable_eq(self.p_square.as_ref().to_le_bytes().as_ref(), a.as_ref());

    let b_abs = b_abs.as_ref();

    let b_abs = {
      /*
        We use the little-endian encoding of the absolute value of the discriminant as we know it
        will have sufficient size to contain the `b` coefficient, bounded to be less than the
        square root of the discriminant.
      */
      let mut repr = self.absolute_value.to_le_bytes();
      // Zeroize the representation
      {
        let repr = repr.as_mut();
        for b in repr.iter_mut() {
          *b = 0;
        }
        // Set it to the `b` coefficient
        let mutual_len = repr.len().min(b_abs.len());
        repr[.. mutual_len].copy_from_slice(&b_abs[.. mutual_len]);
      }
      Udp::from_le_bytes(repr)
    };

    let x_tilde = b_abs.clone().div(self.fundamental.p.as_nz_ref());
    let correct_b_coefficient = x_tilde.clone().mul(self.fundamental.p.as_ref()).ct_eq(&b_abs);

    let x_tilde = x_tilde.to_le_bytes();
    let x_tilde = {
      // `x_tilde <= p` per Proposition 1 of Linearly Homomorphic Encryption from DDH
      let x_tilde = x_tilde.as_ref();
      let mut p_repr = self.fundamental.p.as_ref().to_le_bytes();
      {
        let p_repr = p_repr.as_mut();
        for b in p_repr.iter_mut() {
          *b = 0;
        }
        let mutual_len = p_repr.len().min(x_tilde.len());
        p_repr[.. mutual_len].copy_from_slice(&x_tilde[.. mutual_len]);
      }
      Up::from_le_bytes(p_repr)
    };
    let inverse =
      Up::ct_select(&x_tilde.neg_mod(self.fundamental.p.as_nz_ref()), &x_tilde, b_positive)
        .invert_mod(self.fundamental.p.as_nz_ref())
        .filter_by(correct_discriminant & correct_a_coefficient & correct_b_coefficient);
    inverse.or(CtOption::new(
      Up::zero_like(self.fundamental.p.as_ref()),
      correct_discriminant & element.is_identity(),
    ))
  }
}
