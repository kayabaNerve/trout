//! Methods for sampling and working with discriminants (and the maps between them)
//!
//! We specifically provide the maps from
//! "A Cryptosystem Based on Non-maximal Imaginary Quadratic Orders with Fast Decryption" by
//! Detlef Hühnlein, Michael J. Jacobson, Jr., Sachar Paulus, and Tsuyoshi Takagi
//! (<https://link.springer.com/content/pdf/10.1007/bfb0054134.pdf>). These maps traditionally note
//! the prime conductor as `q`, yet the following implementations consistently denote it as `p`.
//! This is as "Linearly Homomorphic Encryption from DDH"
//! by Guilhem Castagnos and Fabien Laguillaumie (<https://eprint.iacr.org/2025/047>) denote the
//! prime conductor as `p` and we prefer consistency with the latter paper.
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
  Choice, CtOption, CtEq, CtGt, CtSelect, CtAssign, Zero, One, NonZero, Odd, Limb, CheckedAdd,
  CheckedSub, Mul, ConcatenatingMul, ConcatenatingSquare, Div, Rem, NegMod, MulMod, SquareMod,
  InvertMod, BitOps, Encoding, RandomBits, RandomMod, UnsignedWithMontyForm,
};

use crate::Element;

/// For a primitive reduced positive definite form of negative discriminant, return the
/// equivalent form whose `a` coefficient is coprime to the prime `p`.
///
/// `p` MUST be prime. The inputs MUST have sufficient capacity to calculate `a + b + c, b + 2 a`.
/// Additionally, `a, b, c` MUST be of the same size.
///
/// This function runs in constant time. It WILL NOT return `None` if the inputs are satisfied but
/// MAY return `None` if for invalid inputs, if it fails to find an equivalent form with a coprime
/// `a` coefficient.
#[must_use]
fn coprime_form<
  Up: Zero,
  U: Clone + AsRef<[Limb]> + AsMut<[Limb]> + CtSelect + for<'a> Rem<&'a NonZero<Up>, Output: Zero>,
>(
  mut a: U,
  (mut b_positive, mut b_abs): (Choice, U),
  mut c: U,
  p: &NonZero<Up>,
) -> CtOption<(U, (Choice, U))> {
  let a_is_coprime = !a.clone().rem(p).is_zero();
  let c_is_coprime = !c.clone().rem(p).is_zero();

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

  correct &= !a.clone().rem(p).is_zero();
  CtOption::new((a, (b_positive, b_abs)), correct)
}

/// Check if two little-endian encodings represent the same number.
///
/// This function runs in time independent to the encoded values and is considered to run in
/// constant time, though it is in time variable to the lengths of the inputs (which are not
/// considered secrets).
///
/// This function does not check the encodings are canonical and does allow trailing zero bytes.
#[must_use]
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
  /// This returns `k` such that $2^k$ is greater than or equal to the order (class
  /// number) of this group. The returned `k` is not required to be minimal or calculated by any
  /// specific formula, so long as $2^k$ is greater than or equal to a proven bound on the order of
  /// this group.
  ///
  /// The provided implementation runs in variable time. The provided implementation MAY panic if
  /// this discriminant is ill-defined or absurdly large.
  #[must_use]
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
  #[must_use]
  fn absolute_value(&self) -> impl AsRef<[u8]>;
}
/// An odd discriminant.
pub trait OddDiscriminant: Discriminant {}
/// A fundamental (square-free) discriminant.
pub trait FundamentalDiscriminant: Discriminant {
  /// Take an element of the class group with fundamental discriminant and apply the injection such
  /// that it is mapped to an element of a class group with a non-fundamental discriminant.
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
  /// `Udk` MUST be large enough to store the absolute value of this discriminant. `p` MUST be
  /// prime. This function MAY panic or return an incorrect result if `element` is not of this
  /// discriminant. This function runs in time only variable to the discriminant, the length of the
  /// encoding of `p`, and `E::a_b_c_discriminant` (which may be implemented in constant-time).
  #[must_use]
  #[expect(private_bounds)]
  fn inject<
    Up: Zero + ConcatenatingSquare,
    Udk: AsRef<[Limb]>
      + ConcatenatingMul<
        <Up as ConcatenatingSquare>::Output,
        Output: AsRef<[Limb]>
                  + AsMut<[Limb]>
                  + for<'a> Mul<
          &'a Up,
          Output = <Udk as ConcatenatingMul<<Up as ConcatenatingSquare>::Output>>::Output,
        > + for<'a> Rem<&'a NonZero<Up>, Output: Zero>
                  + BitOps
                  + Encoding
                  + RandomBits
                  + crate::crypto_bigint::c::Limbs
                  + crate::crypto_bigint::reduction::Limbs,
      > + Encoding
      + RandomBits,
    E: Element,
  >(
    &self,
    element: impl Element,
    p: &NonZero<Up>,
  ) -> E
  where
    Self: NegativeDiscriminant,
  {
    let (a, (b_positive, b_abs), c, discriminant_abs) = element.a_b_c_discriminant();
    let a: &[u8] = a.as_ref();
    let b_abs: &[u8] = b_abs.as_ref();
    let c: &[u8] = c.as_ref();
    let discriminant_abs: &[u8] = discriminant_abs.as_ref();

    assert!(bool::from(le_malleable_eq(self.absolute_value().as_ref(), discriminant_abs)));

    type Udp<Up, Udk> = <Udk as ConcatenatingMul<<Up as ConcatenatingSquare>::Output>>::Output;

    // This is only vartime with regards to the length of the encoding
    fn Ux_from_bytes<Ux: AsRef<[Limb]> + Encoding + RandomBits>(
      bytes: &[u8],
      bits_precision: u32,
    ) -> Ux {
      let mut repr = Ux_zero_with_precision::<Ux>(bits_precision).to_le_bytes();
      {
        let repr: &mut [u8] = repr.as_mut();
        let mutual_len = bytes.len().min(repr.len());
        repr[.. mutual_len].copy_from_slice(&bytes[.. mutual_len]);
        let mut remaining = Limb::ZERO;
        for b in &bytes[mutual_len ..] {
          remaining |= Limb::from(*b);
        }
        assert!(bool::from(remaining.is_zero()), "`Ux` could not fit this value");
      }
      Ux::from_le_bytes(repr)
    }

    let discriminant_abs = Ux_from_bytes::<Udk>(
      discriminant_abs,
      8 * u32::try_from(discriminant_abs.as_ref().len()).unwrap(),
    );
    let discriminant_abs = discriminant_abs.concatenating_mul(p.concatenating_square());

    let bits_precision = discriminant_abs.bits_precision();
    let a = Ux_from_bytes::<Udp<Up, Udk>>(a, bits_precision);
    let b_abs = Ux_from_bytes::<Udp<Up, Udk>>(b_abs, bits_precision);
    let c = Ux_from_bytes::<Udp<Up, Udk>>(c, bits_precision);

    /*
      `coprime_form` requires these numbers have the capacity for `a + b + c` and `b + 2 a`. As
      these numbers fit in `Udk`, yet this is over `Udp` which is at least two bits larger (due to
      the smallest prime being `2`), the results will fit in `Udp`.
    */
    let (a, (b_positive, b_abs)) = coprime_form::<Up, Udp<Up, Udk>>(a, (b_positive, b_abs), c, p)
      .expect("could not find a coprime form (non-primitive or unreduced?)");

    /*
      `b_abs` as output from `coprime_form`, is bound to be less than or equal to `3 a` (for the
      input `a`, not the output `a`). That means `b_abs` is less than the fundamental
      discriminant's absolute value so long as the fundamental discriminant's absolute value is
      greater than or equal to `9`. If the fundamental discriminant's absolute value is less than
      `9`, than this will fit in the padding due to having such a small value in relation to to the
      size of a `Limb` (at least 16 bits).

      `b_abs * p` will then fit in `Udp` as `Udp` can fit the fundamental discriminant's absolute
      values multiplied by `p^2`.
    */
    let b_abs = b_abs * p.as_ref();

    // `max(a, |b|) < |discriminant|` so long as `discriminant <= -9`, as per prior commentary
    let log_2_bound = discriminant_abs.bits_precision() - 1;
    /*
      The form is valid. The numbers are within `log_2_bound`. The numbers are the same size, and
      with a spare bit of capacity. This causes our call to `partial_reduce` to be valid.
    */
    let (a, (b_positive, b_abs), c) =
      crate::crypto_bigint::partial_reduce(log_2_bound, a, (b_positive, b_abs), &discriminant_abs);
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
        &c.to_le_bytes().as_ref()[.. discriminant_bits.div_ceil(8)],
        &discriminant_abs.to_le_bytes().as_ref()[.. discriminant_bits.div_ceil(8)],
      )
    }
  }
}

struct WithoutTrailingZeroBytes<B: AsRef<[u8]>>(B);
impl<B: AsRef<[u8]>> AsRef<[u8]> for WithoutTrailingZeroBytes<B> {
  fn as_ref(&self) -> &[u8] {
    let mut bytes = self.0.as_ref();
    while bytes.last() == Some(&0) {
      bytes = &bytes[.. (bytes.len() - 1)];
    }
    bytes
  }
}

/// A fundamental discriminant as part of the CL15 cryptosystem.
///
/// This is constructed as detailed in "Linearly Homomorphic Encryption from DDH" by
/// Guilhem Castagnos and Fabien Laguillaumie (<https://eprint.iacr.org/2025/047>), corresponding
/// to $\Delta_K$.
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
  /// This runs in time variable to the bit-length of the discriminant.
  fn absolute_value(&self) -> impl AsRef<[u8]> {
    WithoutTrailingZeroBytes(self.absolute_value.to_le_bytes())
  }
}
impl<Up, Udk> OddDiscriminant for Cl15k<Up, Udk> {}
impl<Up, Udk> FundamentalDiscriminant for Cl15k<Up, Udk> {}

impl<Up, Udk> Cl15k<Up, Udk> {
  /// The prime `p` from the setup.
  #[must_use]
  pub fn p(&self) -> &Odd<Up> {
    &self.p
  }
}

/// A non-fundamental discriminant as part of the CL15 cryptosystem.
///
/// This is constructed as detailed in Linearly Homomorphic Encryption from DDH by
/// Guilhem Castagnos and Fabien Laguillaumie (<https://eprint.iacr.org/2025/047>), correspond to
/// $\Delta_p$.
///
/// `Up` is the numeric type used to represent the prime `p`. `Udk` is the numeric type used to
/// represent the fundamental discriminant's absolute value, the product $q * p$. `Udp` is the
/// numeric type used to represent the non-fundamental discriminant's absolute value, the product
/// $q * p^3$.
#[derive(Clone)]
pub struct Cl15p<Up, Up2, Udk, Udp> {
  fundamental: Cl15k<Up, Udk>,
  p_square: Up2,
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

  /// This runs in time variable to the bit-length of the discriminant.
  fn absolute_value(&self) -> impl AsRef<[u8]> {
    WithoutTrailingZeroBytes(self.absolute_value.to_le_bytes())
  }
}
impl<Up, Up2, Udk, Udp> OddDiscriminant for Cl15p<Up, Up2, Udk, Udp> {}

/// An error when sampling discriminants for the CL15 cryptosystem.
#[derive(Debug)]
pub enum Cl15Error {
  /// The odd prime `p` was too small.
  SmallP,
  /// There were no candidates for the odd prime `q`.
  ///
  /// In effect, this means the fundamental discriminant was too small with regards to the
  /// specified odd prime `p`.
  NoQ,
}

/// The parameters for the fundamental discriminant within the CL15 cryptosystem.
pub struct Cl15kParameters<Udk> {
  /// The smallest integer such that
  /// $\lfloor \mathsf{log}_2(p * q) \rfloor + 1 = \mathsf{fundamental_discriminant_bit_length}$.
  q_min: Udk,

  /// The largest integer such that
  /// $\lfloor \mathsf{log}_2(p * q) \rfloor + 1 = \mathsf{fundamental_discriminant_bit_length}$.
  q_max: Udk,
}

/// A $q'$ value to derive a fundamental discriminant from.
pub struct QApostraphe<Udk> {
  parameters: Cl15kParameters<Udk>,
  q_apostraphe: Udk,
}

impl<Udk: CtGt + CheckedAdd + CheckedSub + BitOps + Encoding> Cl15kParameters<Udk> {
  /// Sample a $q'$ within these parameters.
  ///
  /// This denotes $q'$, traditionally read "q prime", as "q apostraphe" as we do not wish to
  /// suggest this value is prime. Statistically, it is not, even though it will be used to sample
  /// a $q$ which is prime.
  ///
  /// We denote $q_\mathsf{max} - q_\mathsf{min}$ as a $k$-bit number. This reads
  /// $\lfloor k / 8 \rfloor$ bytes from the RNG and interprets them as the little-endian
  /// representation of a number $n$. If $0 \le n \le q_\mathsf{max} - q_\mathsf{min}$, then $n$ is
  /// returned. Else, the sample process repeats until it yields such an $n$, which is likely to
  /// happen within a few hundred iterations at worst.
  ///
  /// This returns `None` if the set of candidates for `q` is empty.
  ///
  /// This function runs in variable time.
  pub fn sample_q_apostraphe(self, mut rng: impl CryptoRng) -> CtOption<QApostraphe<Udk>> {
    self.q_max.checked_sub(&self.q_min).map(|sample_range| {
      let mut starting_point_in_range = sample_range.to_le_bytes();
      for b in starting_point_in_range.as_mut() {
        *b = 0;
      }
      while {
        rng.fill_bytes(
          &mut starting_point_in_range.as_mut()
            [.. usize::try_from(sample_range.bits_vartime().div_ceil(8)).unwrap()],
        );
        bool::from(Udk::from_le_bytes(starting_point_in_range.clone()).ct_gt(&sample_range))
      } {}
      let starting_point_in_range = Udk::from_le_bytes(starting_point_in_range);

      let q_apostraphe = self
        .q_min
        .checked_add(&starting_point_in_range)
        .expect("result is less than or equal to `q_max`, which has the same capacity");
      QApostraphe { parameters: self, q_apostraphe }
    })
  }
}

// TODO: https://github.com/RustCrypto/crypto-bigint/issues/1275
#[allow(non_snake_case)]
fn Ux_zero_with_precision<Udk: AsRef<[Limb]> + RandomBits>(bits_precision: u32) -> Udk {
  struct Zero;
  impl crypto_bigint::rand_core::TryRng for Zero {
    type Error = crypto_bigint::rand_core::Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
      Ok(0)
    }
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
      Ok(0)
    }
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
      for b in dst {
        *b = 0;
      }
      Ok(())
    }
  }
  let result = Udk::random_bits_with_precision(&mut Zero, 0, bits_precision);
  {
    let mut zero = Limb::ZERO;
    for limb in <_ as AsRef<[Limb]>>::as_ref(&result) {
      zero |= *limb;
    }
    debug_assert!(bool::from(zero.is_zero()));
  }
  result
}

impl<
  Up: Clone
    + AsRef<[Limb]>
    + AsMut<[Limb]>
    + CtAssign
    + Zero
    + One
    + NegMod<Output = Up>
    + MulMod<Output = Up>
    + SquareMod<Output = Up>
    + ConcatenatingSquare
    + BitOps,
  Udk: Clone
    + AsRef<[Limb]>
    + AsMut<[Limb]>
    + CtGt
    + One
    + CheckedAdd
    + CheckedSub<Udk>
    + for<'a> Mul<&'a Up, Output = Udk>
    // TODO: `for<'a> ConcatenatingMul<&'a <Up as ConcatenatingSquare>::Output, Output: 'static>`
    + ConcatenatingMul<<Up as ConcatenatingSquare>::Output>
    + for<'a> Div<&'a NonZero<Up>, Output = Udk>
    + for<'a> Rem<&'a NonZero<Up>, Output = Up>
    + BitOps
    + Encoding
    + RandomBits
    + RandomMod
    + UnsignedWithMontyForm,
>
  Cl15p<
    Up,
    <Up as ConcatenatingSquare>::Output,
    Udk,
    <Udk as ConcatenatingMul<<Up as ConcatenatingSquare>::Output>>::Output,
  >
{
  /// Derive parameters to sample a fundamental discriminant with, as described by the `Gen`
  /// algorithm of CL15.
  ///
  /// This function runs in time variable to `fundamental_discriminant_bit_length`.
  pub fn sample_parameters(
    fundamental_discriminant_bit_length: u32,
    p: &Odd<Up>,
  ) -> Result<Cl15kParameters<Udk>, Cl15Error> {
    /*
      Find the lowest, highest numbers `q` could be while still effecting the desired bit-length
      of the fundamental_discriminant.

      The lower bound is `(1 << (fundamental_discriminant_bit_length - 1)) / p`.
      The upper bound is `((1 << fundamental_discriminant_bit_length) - 1) / p`.
    */
    let mut lower_bound_inclusive =
      Ux_zero_with_precision::<Udk>(fundamental_discriminant_bit_length);
    lower_bound_inclusive.set_bit(fundamental_discriminant_bit_length - 1, Choice::TRUE);
    debug_assert_eq!(lower_bound_inclusive.bits_vartime(), fundamental_discriminant_bit_length);
    lower_bound_inclusive = lower_bound_inclusive / p.as_nz_ref();

    let mut upper_bound_inclusive =
      Ux_zero_with_precision::<Udk>(fundamental_discriminant_bit_length);
    for bit in 0 .. fundamental_discriminant_bit_length {
      upper_bound_inclusive.set_bit(bit, Choice::TRUE);
    }
    debug_assert_eq!(upper_bound_inclusive.bits_vartime(), fundamental_discriminant_bit_length);
    upper_bound_inclusive = upper_bound_inclusive / p.as_nz_ref();

    // Require `q >= 4 p` (which is not prime, inherently effecting `q > 4 p`)
    {
      let lower_bound_inclusive_lt_4p = {
        let lower_bound_inclusive = <_ as AsRef<[Limb]>>::as_ref(&lower_bound_inclusive);
        let p = <_ as AsRef<[Limb]>>::as_ref(&p);

        let mut borrow = Limb::ZERO;
        let mut carry = Limb::ZERO;
        /*
          The virtual length is the greater length between the two numbers, though we assign an
          extra virtual limb to `p` as `4 p` may require more limbs to represent. The iterators
          over the numbers' limbs are extended with `0` up to the virtual length.
        */
        let virtual_len = lower_bound_inclusive.len().max(1 + p.len());
        for (lower_bound_inclusive, p) in lower_bound_inclusive
          .iter()
          .chain(core::iter::repeat(&Limb::ZERO))
          .take(virtual_len)
          .zip(p.iter().chain(core::iter::repeat(&Limb::ZERO)).take(virtual_len))
        {
          let four_p = ((*p) << 2) | carry;
          carry = (*p) >> (Limb::BITS - 2);
          let _diff_limb;
          (_diff_limb, borrow) = lower_bound_inclusive.borrowing_sub(four_p, borrow);
        }
        debug_assert!(bool::from(carry.is_zero()));
        !borrow.is_zero()
      };

      // If `lower_bound_inclusive < 4 p`, set `lower_bound_inclusive = 4 p`
      if bool::from(lower_bound_inclusive_lt_4p) {
        if (2 + p.bits_vartime()) > fundamental_discriminant_bit_length {
          Err(Cl15Error::NoQ)?;
        }
        let mut lower_bound_inclusive =
          <_ as AsMut<[Limb]>>::as_mut(&mut lower_bound_inclusive).iter_mut();
        let p = <_ as AsRef<[Limb]>>::as_ref(&p);
        let mut carry = Limb::ZERO;
        for (lower_bound_inclusive, p) in (&mut lower_bound_inclusive).zip(p) {
          let four_p = ((*p) << 2) | carry;
          carry = (*p) >> (Limb::BITS - 2);
          *lower_bound_inclusive = four_p;
        }
        if bool::from(!carry.is_zero()) {
          *lower_bound_inclusive.next().unwrap() = carry;
        }
      }
    }

    Ok(Cl15kParameters { q_min: lower_bound_inclusive.clone(), q_max: upper_bound_inclusive })
  }

  /// Derive a fundamental discriminant from a $q'$.
  ///
  /// `bits_of_security` DOES NOT correspond to the hardness of finding the order of the resulting
  /// group. `bits_of_security` is used to configure the primality tests and for the requirement
  /// $p > 2^{bits_of_security}$, as (loosely) required for a $2^{-bits_of_security}$ likelihood
  /// the that unknown order is divisible by `p` (a requirement of the cryptosystem). The relation
  /// of `bits_of_security` to `fundamental_discriminant_bit_length` is completely unchecked.
  ///
  /// `fundamental_discriminant_bit_length` will the bit-length of the fundamental discriminant.
  /// `1827` is SUGGESTED as the bit-length of the fundamental discriminant for 128-bit security.
  /// Please review <https://eprint.iacr.org/2020/196> for context on choices.
  ///
  /// `p` MUST be an odd prime and is specified by its little-endian encoding. It is undefined
  /// behavior to specify a `p` which is not actually an odd prime.
  ///
  /// The result is completely deterministic to the parameters, except with statistical
  /// negligibility (if the primality tests disagree). The RNG is only used for entropy for said
  /// primality tests.
  ///
  /// This function runs in variable time.
  /*
    TODO: While primality tests will reject primes without such confidence, that's distinct from
    saying primality tests disagree only with such statistical negligibility.
  */
  // TODO: `OddPrime` which is `unsafe` to construct then this which is safe?
  pub fn derive(
    mut rng: impl CryptoRng,
    bits_of_security: u32,
    fundamental_discriminant_bit_length: u32,
    p: Odd<Up>,
    q_apostraphe: QApostraphe<Udk>,
  ) -> Result<Self, Cl15Error> {
    {
      let mu = p.as_ref().bits_vartime();
      /*
        $mu = \lfloor log_2(p) \rfloor + 1$, so to check $p \ge 2^{bits_of_security}$, we need to
        check $\floor log_2(p) \rfloor \ge bits_of_security$.

        As cited in Linearly Homomorphic Encryption from DDH, Conjecture 5.10.1 (Cohen-Lenstra) of
        A Course in Computational Algebraic Number Theory establishes the probability an odd prime
        divides the order as $1 - \prod_{1 \le k \le \inf} (1 - p^{-k})$. It's clear that each
        factor is less than one and therefore the product gets smaller and smaller. For simplicity,
        we limit the expression to solely $k = 1$ and consider solely $1 - (1 - p^{-1})$ which is
        equal to probability $1 / p$. In this case, it's clear how requiring the odd prime $p$ to
        be greater than $2^{bits_of_security}$ is sufficient to achieve this goal. While a tighter
        bound is possible, we do not bother here.
      */
      if (mu - 1) < bits_of_security {
        Err(Cl15Error::SmallP)?;
      }
    }

    let q = {
      let QApostraphe {
        parameters: Cl15kParameters { q_min: lower_bound_inclusive, q_max: upper_bound_inclusive },
        q_apostraphe: mut seed,
      } = q_apostraphe;
      let mut lower_bound_inclusive = Some(lower_bound_inclusive);
      loop {
        let q = match super::primes::next_prime(&mut rng, seed.clone(), bits_of_security) {
          Ok(q) => q,
          // If the next `q` would be too big, loop around to the smallest candidate
          Err(super::primes::Error::Capacity) => {
            // If we've looped multiple times, there are no numbers satisfying `q`
            seed = lower_bound_inclusive.take().ok_or(Cl15Error::NoQ)?;
            continue;
          }
          // While there may be a `q`, we are unable to find it with the requirements given to us
          Err(super::primes::Error::NoMillerRabin) => Err(Cl15Error::NoQ)?,
        };

        if bool::from(q.ct_gt(&upper_bound_inclusive)) {
          seed = lower_bound_inclusive.take().ok_or(Cl15Error::NoQ)?;
          continue;
        }

        // In case this `q` isn't selected, advance the seed to `q + 1`
        seed = match Option::<Udk>::from(q.checked_add(&Udk::one())) {
          Some(q_plus_one) => q_plus_one,
          // This `q` is within bounds but the next seed loops around to the lower bound
          None => lower_bound_inclusive.take().ok_or(Cl15Error::NoQ)?,
        };

        /*
          Discriminants must be congruent to $0$ or $3 \mod 4$, here the latter.

          We only take the product of the very first limb, effectively reducing `p, q` by
          $2^{Limb::BITS}$, as we only need what the result is congruent to $\mod 4$. This is
          reduction preserves the desired congruency so long as `Limb::BITS >= 2`.
        */
        const {
          assert!(Limb::BITS >= 2);
        }
        if {
          let product =
            <_ as AsRef<[Limb]>>::as_ref(&p)[0].wrapping_mul(<_ as AsRef<[Limb]>>::as_ref(&q)[0]);
          (product.0 & 0b11) != 0b11
        } {
          continue;
        }

        /*
          Ensure $p$ is a quadratic non-residue modulo $q$, as specified within CL15's `Gen`
          algorithm. The stated reason is so the 2-Sylow subgroup is isomorphic to $Z/2Z$ (stated
          to require $legendre(p, q) = legendre(q, p) = -1$).

          Note per quadratic reciprocity, $legendre(p, q) = legendre(q, p)$ if and only if not both
          $p, q$ are congruent to $3 \mod 4$. As their product is congruent to $3 \mod 4$, they
          cannot each simultaneously be congruent to $3 \mod 4$, as $3 \mod 4$ is not a square.
          This allows us to solely check one Legendre symbol.

          With this in mind, we actually check $q$ is a quadratic non-residue modulo $p$ as $p$ is
          a smaller number and therefore offers faster arithmetic to perform the check with.
        */
        if {
          let q_mod_p = q.clone().rem(p.as_nz_ref());
          crate::crypto_bigint::legendre_symbol(q_mod_p, &p) !=
            ::crypto_bigint::JacobiSymbol::MinusOne
        } {
          continue;
        }

        break q;
      }
    };

    let fundamental_discriminant_absolute_value = q.mul(p.as_ref());
    debug_assert_eq!(
      fundamental_discriminant_absolute_value.bits_vartime(),
      fundamental_discriminant_bit_length
    );

    let p_square = p.as_ref().concatenating_square();

    let non_fundamental_discriminant_absolute_value =
      fundamental_discriminant_absolute_value.concatenating_mul(p_square.clone());

    Ok(Cl15p {
      fundamental: Cl15k { p, absolute_value: fundamental_discriminant_absolute_value },
      p_square,
      absolute_value: non_fundamental_discriminant_absolute_value,
    })
  }

  /// Sample a fundamental discriminant as described by the `Gen` algorithm of CL15.
  ///
  /// This function is a composition of [`Cl15p::sample_parameters`],
  /// [`Cl15kParameters::sample_q_apostraphe`], and [`Cl15p::derive`], using the provided RNG both
  /// to sample $q'$ and as entropy for the primality tests. Please read those methods'
  /// documentation to understand the bounds on and expectations of this method.
  ///
  /// This function runs in variable time.
  pub fn sample(
    mut rng: impl CryptoRng,
    bits_of_security: u32,
    fundamental_discriminant_bit_length: u32,
    p: Odd<Up>,
  ) -> Result<Self, Cl15Error> {
    let parameters = Self::sample_parameters(fundamental_discriminant_bit_length, &p)?;
    let q_apostraphe = Option::<QApostraphe<Udk>>::from(parameters.sample_q_apostraphe(&mut rng))
      .ok_or(Cl15Error::NoQ)?;
    Self::derive(rng, bits_of_security, fundamental_discriminant_bit_length, p, q_apostraphe)
  }
}

impl<Up, Up2, Udk, Udp> Cl15p<Up, Up2, Udk, Udp> {
  /// The fundamental discriminant.
  #[must_use]
  pub fn fundamental_discriminant(&self) -> &Cl15k<Up, Udk> {
    &self.fundamental
  }
}

impl<Up: Encoding, Up2: Encoding, Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding>
  Cl15p<Up, Up2, Udk, Udp>
{
  /// The element of `p`-order with an easy discrete-log problem.
  ///
  /// This runs in time variable to the bit-length of the discriminant.
  #[must_use]
  pub fn f<E: Element>(&self) -> E {
    /*
      $b^2 + |delta| = 4 a c = p^2 + (q p p^2) = (q p + 1) p^2$
      $a = p^2$ so $c = (q p + 1) / 4$

      This `c` coefficient exists as $q p \cong 3 \mod 4$, per how `q` was chosen during the setup.
    */
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

    let discriminant_abs = WithoutTrailingZeroBytes(self.absolute_value.to_le_bytes());
    let discriminant_abs = discriminant_abs.as_ref();
    let discriminant_bytes = discriminant_abs.len();
    // This is a lossy approximation
    let sqrt_discriminant_bytes = discriminant_bytes.div_ceil(2);

    // We bound the encodings of `a, b, c` based on the discriminant
    let a = self.p_square.to_le_bytes();
    let a = a.as_ref();
    let a = &a[.. sqrt_discriminant_bytes.min(a.len())];

    let b_positive = Choice::TRUE;
    let b_abs = self.fundamental.p.to_le_bytes();
    let b_abs = b_abs.as_ref();
    let b_abs = &b_abs[.. sqrt_discriminant_bytes.min(b_abs.len())];

    let c = c.to_le_bytes();
    let c = c.as_ref();
    let c = &c[.. discriminant_bytes.min(c.len())];

    /*
      SAFETY:

      This form is well-defined, as we defined (and calculated) the satisfactory `c` coefficient
      above.

      This form is primitive as `c = (q p + 1) / 4` and `q p + 1 is coprime to `b = p` when
      $p \ne 1$. If $p \eq 1$, then $b = 1$ and $gcd(a, b, c) = 1$ (and the form is primitive).
      However, as $p$ is an odd prime, the case $p \eq 1$ is unnecessary to argue.

      This form is reduced as $|b| < a, b \ne a$ and $a < sqrt(|delta| / 4)$. For the latter claim,
      we require $q > 4 p$ during our setup, where this discriminant is of form $q p^3$. Therefore,
      $p^2 < sqrt(|delta| / 4)$.
    */
    unsafe { E::from_coefficients(a, (b_positive, b_abs), c, discriminant_abs) }
  }
}

impl<
  Up: AsRef<[Limb]>
    + CtSelect
    + NegMod<Output = Up>
    + for<'a> ConcatenatingMul<&'a Up, Output: Encoding>
    + ConcatenatingSquare<Output: Encoding>
    + InvertMod<Output = Up>
    + BitOps,
  Up2: Encoding,
  Udk: Clone + AsMut<[Limb]> + Encoding,
  Udp: Encoding,
> Cl15p<Up, Up2, Udk, Udp>
{
  /// The element of `p`-order with an easy discrete-log problem, scaled by the scalar `u`.
  ///
  /// This runs in time variable to the bit-length of the discriminant, the length of the encodings
  /// of `Up2, Udk, Udp`. and the length of the encodings of the coefficients for the identity
  /// element as returned by `E::identity(&discriminant_abs).a_b_c_discriminant()`.
  ///
  /// This function assumes $0 \le u < p$.
  #[must_use]
  pub fn f_scaled<E: Element>(&self, u: &Up) -> E {
    /*
      This method effectively performs the opposite of the discrete logarithm function, finding the
      element whose discrete logarithm can be solved for to equal `u`. Its own variables are
      notated to maintain parity with the discrete logairthm function.

      The [BICYCL paper](https://eprint.iacr.org/2022/1466) presents fast exponentations (which we
      notate as multiplications) of `f` and was the inspiration for this method. They do not
      present pseudo-code for their theory and describe their premise in terms of the ideals, while
      this is discussed in terms of the binary quadratic forms. Its correctness is on the premise
      it does output a well-defined, primitive, reduced element of the class group for which the
      discrete logarithm function outputs `u`. However, one can question if the discrete logarithm
      function outputting a solution for this element actually means this element is within the
      subgroup (or if the discrete logarithm simply works for certain elements outside of the
      subgroup it's presented to work with regards to), leaving the correctness of this mildly
      incomplete.
    */
    let a_b_c = u.invert_mod(self.fundamental.p.as_nz_ref()).map(|x_tilde| {
      /*
        $b^2 + |delta| = 4 a c = (x_tilde p)^2 + (q p p^2) = (q p + x_tilde^2) p^2$
        $a = p^2$ so $c = (q p + x_tilde^2) / 4$

        $q p \cong 3 \mod 4$, per how `q` was chosen during the setup. If `x_tilde` is odd, then
        $x_tilde^2 \cong 1 \mod 4$ and $4 | (q p + x_tilde^2)$. If `x_tilde` is even, then we
        negate it and adjust the $b$ coefficient accordingly to ensure it's odd and there is a
        $c$ coefficient.
      */
      let b_positive = (<_ as AsRef<[Limb]>>::as_ref(&x_tilde)[0] & Limb::ONE).ct_eq(&Limb::ONE);
      let x_tilde =
        <_>::ct_select(&x_tilde.neg_mod(self.fundamental.p.as_nz_ref()), &x_tilde, b_positive);
      let b_abs = x_tilde.concatenating_mul(self.fundamental.p.as_ref());

      let c = {
        // `q p`
        let mut c = self.fundamental.absolute_value.clone();
        {
          let c = <_ as AsMut<[Limb]>>::as_mut(&mut c);
          let x_tilde_squared = x_tilde.concatenating_square();
          // `q p` -> `q p + x_tilde^2`
          // `q p > x_tilde^2` as `x_tilde < p < q`
          let mut carry = Limb::ZERO;
          for (c_limb, x_tilde_squared_limb) in c.iter_mut().zip(
            <_ as AsRef<[Limb]>>::as_ref(&x_tilde_squared)
              .iter()
              .chain(core::iter::repeat(&Limb::ZERO)),
          ) {
            let new_limb;
            (new_limb, carry) = c_limb.carrying_add(*x_tilde_squared_limb, carry);
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

      (self.p_square.to_le_bytes(), (b_positive, b_abs.to_le_bytes()), c.to_le_bytes())
    });

    /*
      We cannot call `CtOption::unwrap_or` without:
      1) Binding `E: CtSelect` (when we may want to use `E: !CtSelect`)
      2) Moving the coefficients into a struct which implements `CtSelect` as tuples do not
         (even if their elements do)

      The latter is also non-trivial as we need to select between tuples of encodings, where we
      generally don't bind the lengths of encodings.

      Instead, we directly inspect the `CtOption`'s value, and copy the desired encoding to a
      buffer we know is big enough for any coefficient of any reduced form.
    */

    let not_identity = a_b_c.is_some();
    let (not_identity_a, (not_identity_b_positive, not_identity_b_abs), not_identity_c) =
      a_b_c.as_inner_unchecked();
    let (identity_a, (identity_b_positive, identity_b_abs), identity_c, discriminant_abs) =
      E::identity(self.absolute_value()).a_b_c_discriminant();

    /// Select an encoding, returning a buffer of size `dst` with the selection.
    ///
    /// This function assumes `a.len(), b.len() < dst.len()`.
    ///
    /// If the selected encoding is shorter than `dst`, it is considered to have zeroes for the
    /// missing bytes.
    ///
    /// This function runs in time variable only to the lengths of the arguments, not their values
    /// nor which is chosen.
    fn ct_select_encoding<E: AsMut<[u8]>>(
      mut dst: E,
      a: impl AsRef<[u8]>,
      b: impl AsRef<[u8]>,
      choice: Choice,
    ) -> E {
      {
        let dst = dst.as_mut();
        let a = a.as_ref();
        let b = b.as_ref();

        for (i, byte) in dst.iter_mut().enumerate() {
          *byte = <_>::ct_select(a.get(i).unwrap_or(&0), b.get(i).unwrap_or(&0), choice);
        }
      }
      dst
    }

    // We use the discriminant's encoding as the buffer to write to as we know the
    // discriminant to exceed the size of any coefficient of a reduced form
    let a = ct_select_encoding(
      self.absolute_value.to_le_bytes(),
      identity_a,
      not_identity_a,
      not_identity,
    );
    let b_positive = Choice::ct_select(&identity_b_positive, not_identity_b_positive, not_identity);
    let b_abs = ct_select_encoding(
      self.absolute_value.to_le_bytes(),
      identity_b_abs,
      not_identity_b_abs,
      not_identity,
    );
    let c = ct_select_encoding(
      self.absolute_value.to_le_bytes(),
      identity_c,
      not_identity_c,
      not_identity,
    );

    // We bound the encodings of `a, b, c` based on the discriminant
    let discriminant_abs = WithoutTrailingZeroBytes(discriminant_abs);
    let discriminant_abs = discriminant_abs.as_ref();
    let discriminant_bytes = discriminant_abs.len();
    // This is a lossy approximation
    let sqrt_discriminant_bytes = discriminant_bytes.div_ceil(2);

    let a = a.as_ref();
    let a = &a[.. sqrt_discriminant_bytes.min(a.len())];
    let b_abs = b_abs.as_ref();
    let b_abs = &b_abs[.. sqrt_discriminant_bytes.min(b_abs.len())];
    let c = c.as_ref();
    let c = &c[.. discriminant_bytes.min(c.len())];

    /*
      SAFETY:

      If this form _was not_ the identity:

        This form is well-defined, as we defined (and calculated) the satisfactory `c`
        coefficient above.

        This form is primitive as `c = (q p + x_tilde^2) / 4` and `x_tilde` is coprime to `p`
        (as `p` is an odd prime and `0 < x_tilde < p`, `0 < x_tilde` as this is the branch where
        `x_tilde` has a multiplicative inverse and is therefore not congruent to `0` modulo `p`).

        This form is reduced as $|b| < a, b \ne a$ and $a < sqrt(|delta| / 4)$. For the latter
        claim, we require $q > 4 p$ during our setup, where this discriminant is of form $q p^3$.
        Therefore, $p^2 < sqrt(|delta| / 4)$.

      If the form _was_ the identity:

        We explicitly set the encoding to the identity, which is a well-defined, primitive, reduced
        form.
    */
    unsafe { E::from_coefficients(a, (b_positive, b_abs), c, discriminant_abs) }
  }
}

#[cfg(feature = "alloc")] // TODO: no-`alloc`
impl<
  Up: AsRef<[Limb]> + Zero + BitOps + Encoding,
  Up2,
  Udk: Clone + AsMut<[Limb]> + Encoding,
  Udp: Encoding,
> Cl15p<Up, Up2, Udk, Udp>
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
  #[must_use]
  pub fn surject<E: Element>(&self, element: impl Element) -> E {
    use crypto_bigint::{Resize as _, BoxedUint};

    let (a, (b_positive, b_abs), c, discriminant_abs) = element.a_b_c_discriminant();
    assert!(bool::from(le_malleable_eq(self.absolute_value().as_ref(), discriminant_abs.as_ref())));

    // This is only vartime with regards to the length of the encoding
    let a = BoxedUint::from_le_slice_vartime(a.as_ref());
    let b_abs = BoxedUint::from_le_slice_vartime(b_abs.as_ref());
    let c = BoxedUint::from_le_slice_vartime(c.as_ref());
    let p = &self.fundamental.p;

    let bits_precision = 2 + a.bits_precision().max(b_abs.bits_precision()).max(c.bits_precision());
    let (a, (mut b_positive, b_abs)) = coprime_form(
      a.resize(bits_precision),
      (b_positive, b_abs.resize(bits_precision)),
      c.resize(bits_precision),
      &NonZero::new(BoxedUint::from(<_ as AsRef<[Limb]>>::as_ref(p.as_ref()))).unwrap(),
    )
    .expect("could not find a coprime form (non-primitive or unreduced?)");

    /*
      We calculate our new `b` coefficient modulo `2 a`, which represents an equivalent form.

      We do not consider the `fundamental_discriminant % 2` term as we know the fundamental
      discriminant to be odd, and therefore the term to be equal to `1`, which is the identity (as
      it's used in a multiplication).

      We do not calculate `a * lambda` but solely `a * (lambda & 1)`, as we know `a` generates a
      `2`-subgroup of `2 a` with addition. However, as we have `(mu * p) - 1 = lambda * a`, we also
      know that the trailing zero bits in `(mu * p) - 1` is equal to the trailing zero bits in
      `lambda * a`. This lets us determine `(lambda & 1) == 0` as
      `trailing_zeroes((mu * p) - 1) > trailing_zeroes(a)`.
    */
    let b_abs = {
      let p = BoxedUint::from(<_ as AsRef<[Limb]>>::as_ref(p));
      let bits_precision = a.bits_precision().max(p.bits_precision());
      let p = p.resize(bits_precision);
      let a = NonZero::new(a.clone().resize(bits_precision))
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

      This form is well-defined (TODO).

      This form is primitive as it has a fundamental discriminant. Per a remark following
      Definition 5.2.3 of A Course in Computational Algebraic Number Theory by Henri Cohen,
      any quadratic form of fundamental discriminant is primitive.

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

#[cfg(feature = "alloc")] // TODO: no-`alloc`
#[expect(private_bounds)]
impl<
  Up: AsRef<[Limb]> + Zero + ConcatenatingSquare + BitOps + Encoding,
  Up2,
  Udk: Clone
    + AsRef<[Limb]>
    + AsMut<[Limb]>
    + ConcatenatingMul<
      <Up as ConcatenatingSquare>::Output,
      Output: AsRef<[Limb]>
                + AsMut<[Limb]>
                + for<'a> Mul<
        &'a Up,
        Output = <Udk as ConcatenatingMul<<Up as ConcatenatingSquare>::Output>>::Output,
      > + for<'a> Rem<&'a NonZero<Up>, Output: Zero>
                + BitOps
                + Encoding
                + RandomBits
                + crate::crypto_bigint::c::Limbs
                + crate::crypto_bigint::reduction::Limbs,
    > + Encoding
    + RandomBits,
> Cl15p<Up, Up2, Udk, <Udk as ConcatenatingMul<<Up as ConcatenatingSquare>::Output>>::Output>
{
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
  #[must_use]
  pub fn coset_labeling_function<E: Element>(&self, element: impl Element) -> E {
    self
      .fundamental_discriminant()
      .inject::<Up, Udk, _>(self.surject::<E>(element), self.fundamental.p.as_nz_ref())
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
  /// (<https://eprint.iacr.org/2025/047>). We explicitly specify the calculation of
  /// $\tilde{x}^{-1} \mod p$ via `xgcd(x_tilde, p)` as we've already assumed the existence of an
  /// `xgcd` function elsewhere in our specification, though other methods would work as well and
  /// MAY be used instead (such as by Fermat's Little Theorem or a Bernstein-Yang inversion).
  ///
  /// This function runs time only variable to this discriminant and `E::a_b_c_discriminant` (which
  /// may or may not be implemented in constant-time).
  #[must_use]
  pub fn discrete_logarithm(&self, element: impl Element) -> CtOption<Up> {
    let identity = element.is_identity();
    let (a, (b_positive, b_abs), _c, discriminant_abs) = element.a_b_c_discriminant();

    let correct_discriminant =
      le_malleable_eq(self.absolute_value.to_le_bytes().as_ref(), discriminant_abs.as_ref());
    let correct_a_coefficient = le_malleable_eq(self.p_square.to_le_bytes().as_ref(), a.as_ref());

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
      correct_discriminant & identity,
    ))
  }
}
