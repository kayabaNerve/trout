//! Composition of binary quadratic forms in constant time.
//!
//! This is generic to the underlying container representing the numbers, allowing usage with both
//! allocating and non-allocating backends. However, the module as a whole is in a weird place.
//! Specifically, it optimizes some functions, and leverages incompleteness elsewhere (tailored to
//! the specific special cases encountered during reduction), but the optimized functions are _not_
//! a majority of the runtime (or even a notable part). Instead, the GCD, divisions are, and those
//! are completely deferred. Additionally, despite being generic to the underlying containers and
//! not explicitly allocating, this code does make frequent use of `clone` (presumably copies for
//! elements represented on the stack) due to requiring a non-trivial amount of scratch variables.
//!
//! The important aspect of this code is that it's clearly bounded as necessary to verify the
//! correctness of the implemented algortithm. Despite this, the implemented algorithm is not
//! itself proven here, it being Algorithm 5.4.7 Composition of Positive Definite Forms from
//! A Course in Computational Algebraic Number Theory by Henri Cohen (as commonly implemted in its
//! optimized variant as "NUCOMP").

/*
  The comment composition preserves primitivity is frequently remarked but I (kayabaNerve), can not
  find a single worthwhile citation for that. Cohen left it as an exercise to the reader
  (Chapter 5, Exercise 9). Most literature deals with class groups over fundamental discriminants,
  for which all forms are claimed to be primitive (itself infrequently proven and lacking any
  worthwhile citation), and with little literature for non-fundamental discriminants.

  The NICE cryptosystem did use a non-fundamental discriminant, and included a composition
  algorithm which appears approximate to Algorithm 5.4.7 albeit without `d_0` (as required when
  working with imprimitive forms), implying they solely work with primitive forms, but lacking any
  commentary on the matter.

  "Linearly Homomorphic Encryption from DDH" by Guilhem Castagnos and Fabien Laguillaumie,
  https://eprint.iacr.org/2015/047, does state in Appendix B.1 that the order of the class group
  with non-fundamental discriminant, as they've constructed, has order exactly `p` times greater
  than the order of the class group with fundamental discriminant (which is echoed by a remark
  following the presentation of Algorithm 5.3.5). By Proposition 5.3.3, the order is equivalent to
  the amount of primitive reduced forms, implying all elements we work with are in fact primitive
  (at least, one reduced).

  Due to the ambiguity, and lack of a proof/citation however, the following is a sketch at a proof
  that `gcd(a3, b3, c3) = 1` when the inputs are primitive. While potentially unnecessary due to
  how accepted this result is, and potentially overzealous as we sketch a proof of this but don't
  sketch a proof of the algorithm for composition, it's still included as we do need confidence all
  our forms are primitive. The complexities of working with a non-fundamental discriminant, and
  introducing partial reduction, really require every checkbox is properly ticked.

  As an aside, the reduction algorithm is proven to preserve primitivity in a way which implies if
  reduced forms are primitive, so are non-reduced forms, so a proof reduced forms are primitive
  would be sufficient for our purposes (even without a proof composition outputs primitive forms).
  This aligns with a comment following Definition 5.2.3,
  "One can also easily check that equivalence preserves primitivity". To be complete, we do prove
  both reduction to preserve primitivity (in its location) and composition preserves primitivity
  (with the following sketch).
*/

/*
  The following is solely for the case `a2 = a1, b2 = b1, c2 = c1`, for which we notate
  `a{1, 2}` as `a`, `b{1, 2}` as `b`, and `c{1, 2}` as `c`.

  TODO: Expand to the group operation as a whole.

  `a, b, c` are considered arbitrary integers, with `0 <= a, c`

  `d1 = gcd(a, b)`
  `a3 = (a / d1)^2`
  `r = -u c \mod (a / d1)` where `u` is an integer solution for the equation `ub + va = d1`
  `b3 = b + (a / d1) * r`
  `c3 = (c d1 + r (b + (a / d1) r)) / (a / d1)`

  We wish to prove `gcd(a3, b3, c3) = 1` when `gcd(a, b, c) = 1`.

  We require an identity (which we state and assume but do not prove here):
  - `gcd(x + z * y, y) = gcd(x, y)` for any integer `z` (positive or negative), which we refer to
    as the modular identity due to its corollary `gcd(x % y, y) = gcd(x, y)`
  and the following definition of a three-argument GCD call:
  - `gcd(x, y, z) = gcd(gcd(x, y), z)`

  For the equation `ub + va = d1`, we note that `u, v` are coprime as the equation can be
  rewritten as `(b / d1) u + (a / d1) v = 1`.  Additionally, we know at least one of
  `b / d1, a / d1` is coprime to `d1`, as if neither were, `d1` would not be the GCD of `a, b`.
  We write two proofs for our desired statement, one where `a / d1` is coprime to `d1`, and one
  where `b / d1` is coprime to `d1`.

  When `a / d1` is coprime to `d1`, the proof is quite short.
  - `d1 = gcd(a, b)`
  - By a corollary of the identity `gcd(x * z, y) = gcd(x, y) * gcd(z, y)`, when `z` is coprime
    to `x`, `gcd(a / d1, b) = 1` (as then,
    `gcd(a / d1 * d1, b) = gcd(a / d1, b) * gcd(d1, b) = 1 * d1 = d1`, completing the identity)
  - By the modular identity,
    `gcd(a / d1, b + (a / d1) * r) = gcd(a / d1, b) = gcd(a / d1, b3) = 1`
  - `gcd(a3, b3) = gcd((a / d1)^2, b3) = 1` as `gcd(a / d1, b3) = 1`

  When `b / d1` is coprime to `d1`, the proof is more involved, as `d1` is not cleared from `b`
  during the production of `b3`.

  We define `d1' = gcd(a3, b3) = gcd((a / d1)^2, b)`, with the properties `sqrt(d1') | d1` and
  `d1' | d1^2`. We remember that the input satisfies `gcd(a, b, c) = 1`, and as `gcd(a, b) = d1`,
  then `gcd(d1, c) = 1` must be true. By extension, `gcd(d1', c) = 1`.

  "sqrt" is an absue of notation as `d1'` may not be a square. Here, it's defined such that
  `sqrt(d1')` is the list of _unique_ prime factors in `d1'` such that `sqrt(d1') | d1'`, and
  importantly, `sqrt(d1') | d1`. This lets us establish that being coprime to either `sqrt(d1')`,
  `d1'`, or `d1`, is sufficient to be coprime to `d1'` as required.

  We prove `c3` coprime to `sqrt(d1')` as follows:

  We rewrite `c3 = (c d1 + r (b + (a / d1) r)) / (a / d1)` as:
  - `c3 = (c d1 + r (b + (a / d1) r)) * (d1 / a)`
  - `c3 = (c d1^2 + r (b + (a / d1) r) d1) / a`
  - `c3 = c d1^2 / a + r (b + (a / d1) r) d1 / a`
  - `c3 = c d1^2 / a + (r b + (a / d1) r^2) d1 / a`
  - `c3 = c d1^2 / a + (r b d1 + a r^2) / a`
  - `c3 = c d1^2 / a + r b d1 / a + r^2`
  And apply the modular identity to reduce to just `gcd(r^2, sqrt(d1'))`. We next aim to
  prove `gcd(r, sqrt(d1')) = 1` (and therefore `gcd(r^2, sqrt(d1')) = 1`).

  As `r = -u c \mod (a / d1)`, where `gcd(c, d1) = 1`, we solely have to prove
  `gcd(u, sqrt(d1')) = 1`. Note the operation modulo `a / d1` is congruent as
  `sqrt(d1') | (a / d1)`. As `u` satisfies `ub + va = d1`, we know the derivative equation
  `(b / d1) u + v (a / d1) = 1`, and therefore `gcd(u, a / d1) = 1`. As `sqrt(d1') | (a / d1)`,
  this proves `gcd(u, sqrt(d1')) = 1`, completing the proof `c3` is coprime to `sqrt(d1')`, and
  therefore that `c3` is coprime to `gcd(a3, b3)`.

  This completes the proof that the following doubling algorithm, which outputs `(a3, b3, c3)` as
  described above, preserves primitivity of the input `(a, b, c)`.
*/

use crypto_bigint::{CtEq, CtSelect, CtAssign, Choice, Limb};

use super::I;

/// Calculate half the sum of two signed integers which are congruent modulo two.
///
/// This is equivalent to `(a + b) / 2`, which only has an integer solution when
/// $a \cong b \mod 2$. A wrapping implementation of `a + b`, then divided by two, may be incorrect
/// (due to truncating the highest bit). This ensures a correct solution via the methodology of
/// `(a / 2) + (b / 2)`, adding `1` if $a \cong 1 \mod 2$ (which is guaranteed to fit in the
/// result).
///
/// This is intended to calculate `b_1 + b_2`, as part of composition, where for a binary
/// quadratic form $b^2 - 4ac = delta$, it is apparent how $b \cong delta \mod 2$. Therefore, for
/// any two binary quadratic forms of the same discriminant, their `b` coefficients are congruent
/// modulo two.
///
/// This assigns the absolute value of the result to the first argument. The returned value is if
/// the result is positive. The number `0` MAY be considered positive or negative.
///
/// This assumes `a.1, b.1` have an equivalent amount of limbs.
// NOTE: The composition algorithm requires `2 a` by representable in the container of limbs, so
// we could simplify this algorithm accordingly. This algorithm is a negligible part of the
// reduction, so being complete here is preferred.
fn sum_assign_half_of_two_numbers_congruent_mod_two(
  a: (Choice, &mut [Limb]),
  b: (Choice, &[Limb]),
) -> Choice {
  // This is addition if they have the same sign and subtraction otherwise
  let add = a.0.ct_eq(&b.0);

  /*
    If we are adding two odd numbers, the trailing bits would sum to `2`. As we're calculating
    _half_ the sum, we need to add one to whatever the result is. If we are adding two even
    numbers, the trailing bits sum to `0`, and we do not have to add anything.

    Because we assume these numbers are congruent modulo two, we determine odd/even solely by
    inspecting `a`.

    Note we could minorly optimize this by restricting to odd discriminants, as we do within
    reduction (by simply setting `carry = Limb::ONE`). The assumption in reduction is used to save
    ~5% of the runtime, as it allows deferring when the `b` coefficient is negated. Here, checking
    the least significant bit is trivial, so it's preferable to be complete.
  */
  let mut carry = a.1[0] & Limb::ONE;
  /*
    Because these numbers are congruent modulo 2, their trailing bits are the same and have a
    difference of `0`, so we do not have to do anything about them.
  */
  let mut borrow = Limb::ZERO;

  for i in 0 .. (a.1.len() - 1) {
    let a_shr1: Limb = (a.1[i + 1] << (Limb::BITS - 1)) | (a.1[i] >> 1);
    let b_shr1 = (b.1[i + 1] << (Limb::BITS - 1)) | (b.1[i] >> 1);

    let if_add;
    (if_add, carry) = a_shr1.carrying_add(b_shr1, carry);
    let if_sub;
    (if_sub, borrow) = a_shr1.borrowing_sub(b_shr1, borrow);

    // Write the new limb value
    a.1[i] = Limb::ct_select(&if_sub, &if_add, add);
  }

  {
    let i = a.1.len() - 1;

    let a_shr1: Limb = a.1[i] >> 1;
    let b_shr1 = b.1[i] >> 1;

    let (if_add, _carry) = a_shr1.carrying_add(b_shr1, carry);
    let if_sub;
    (if_sub, borrow) = a_shr1.borrowing_sub(b_shr1, borrow);

    // Write the new limb value
    a.1[i] = Limb::ct_select(&if_sub, &if_add, add);
  }

  let a_gte_b = borrow.is_zero();
  // If this was a subtraction and `a < b`, negate the result
  {
    let a_lt_b = !a_gte_b;
    let mut carry = Limb::from(u8::from(a_lt_b & (!add)));
    let mask = Limb::ZERO.wrapping_sub(carry);
    for limb in a.1 {
      let new_limb;
      (new_limb, carry) = ((*limb) ^ mask).carrying_add(Limb::ZERO, carry);
      *limb = new_limb;
    }
  }

  /*
    `carry` MUST be zero as half the sum of two numbers has at most equal bit-length to the greater
    of the inputs'. `borrow` MAY be non-zero if `a < b`, in which case the result has sign
    equivalent to `b`'s. Specifically, we should output for the sign:

          | Same Sign | Different Signs |
    ------|-----------------------------|
    a < b | a.0 = b.0 |       b.0       |
    a > b | a.0 = b.0 |       a.0       |
    a = b | a.0 = b.0 |        ?        |

    "?" refers to how we are allowed to return either sign for `0`.

    From the above table, it's clear how our choice of which of the inputs' signs is solely
    important when the inputs have different signs, allowing us to very simply define the result.
  */
  Choice::ct_select(&b.0, &a.0, a_gte_b)
}

/// Calculate the difference of two signed integers.
///
/// This assigns the absolute value of the result to the first argument, sans the most significant
/// bit. The returned values are if the result is positive and the most significant bit, in that
/// order. The number `0` MAY be considered positive or negative.
///
/// This assumes `a.1, b.1` have an equivalent amount of limbs and that the result will fit in the
/// same amount of limbs.
fn diff_assign(a: (Choice, &mut [Limb]), b: (Choice, &[Limb])) -> Choice {
  // This is subtraction if they have the same sign and addition otherwise
  let sub = a.0.ct_eq(&b.0);

  let mut carry = Limb::ZERO;
  let mut borrow = Limb::ZERO;
  for (a_limb, b_limb) in a.1.iter_mut().zip(b.1) {
    let if_add;
    (if_add, carry) = a_limb.carrying_add(*b_limb, carry);
    let if_sub;
    (if_sub, borrow) = a_limb.borrowing_sub(*b_limb, borrow);
    *a_limb = Limb::ct_select(&if_add, &if_sub, sub);
  }

  let a_gte_b = borrow.is_zero();
  // If this was a subtraction and `a < b`, negate the result
  {
    let a_lt_b = !a_gte_b;
    let mut carry = Limb::from(u8::from(a_lt_b & sub));
    let mask = Limb::ZERO.wrapping_sub(carry);
    for limb in a.1 {
      let new_limb;
      (new_limb, carry) = ((*limb) ^ mask).carrying_add(Limb::ZERO, carry);
      *limb = new_limb;
    }
  }

  {
    // If we performed an addition, the sign is that of the first number
    let if_add = a.0;
    // If we performed a subtraction, the sign is that of the larger number, but negated if it was
    // the second number
    let if_sub = Choice::ct_select(&!b.0, &a.0, a_gte_b);
    Choice::ct_select(&if_add, &if_sub, sub)
  }
}

/// The result of an extended GCD algorithm.
pub(super) struct Xgcd<U> {
  /// The greatest common denominator.
  pub(super) d: U,
  /// The `u` coefficient such that `ua + vb = d`.
  pub(super) u: I<U>,
  /// The `v` coefficient such that `ua + vb = d`.
  pub(super) v: I<U>,
}

trait LimbHelpers: Sized + AsRef<[Limb]> + AsMut<[Limb]> {
  /// Double the input.
  ///
  /// This assumes the result will fit within the same amount of limbs.
  fn double(mut self) -> Self {
    let mut carry = Limb::ZERO;
    for limb in self.as_mut() {
      let new_limb = ((*limb) << 1) | carry;
      carry = (*limb) >> 63;
      *limb = new_limb;
    }
    #[cfg(debug_assertions)]
    {
      debug_assert!(bool::from(carry.is_zero()));
    }
    self
  }

  /// Negate `self` modulo `modulus` if `negate == true`.
  ///
  /// This assumes `self` and `modulus` have the same amount of limbs and that `self <= modulus`.
  /// This will return if the input was `0` (as an integer, not as congruent to) and the value.
  /// The value may be the modulus (as congruent to `0`) but only if the input was `0` and `negate`
  /// was `true`.
  fn ct_neg_mod(mut self, modulus: &Self, negate: Choice) -> (Choice, Self) {
    let mut is_zero = Limb::ZERO;
    let mut borrow = Limb::ZERO;
    for (our_limb, mod_limb) in self.as_mut().iter_mut().zip(modulus.as_ref()) {
      // Check if the input was zero, which is relatively cheap to do when we're already iterating
      // over this value
      is_zero |= *our_limb;
      let new_limb;
      (new_limb, borrow) = mod_limb.borrowing_sub(*our_limb, borrow);
      our_limb.ct_assign(&new_limb, negate);
    }
    (is_zero.is_zero(), self)
  }

  /// Subtract `b` from `self` modulo `modulus`.
  ///
  /// This assumes `self`, `b`, and `modulus` have the same amount of limbs and both `self` and `b`
  /// are less than or equal to the modulus, and may return the modulus to represent `0` when asked
  /// to calculate `modulus - 0`.
  fn sub_mod(mut self, b: &Self, modulus: &Self) -> Self {
    let mut borrow = Limb::ZERO;
    for (our_limb, b_limb) in self.as_mut().iter_mut().zip(b.as_ref()) {
      let new_limb;
      (new_limb, borrow) = our_limb.borrowing_sub(*b_limb, borrow);
      *our_limb = new_limb;
    }

    // Add the modulus if this underflowed
    let underflowed = !borrow.is_zero();
    let mut carry = Limb::ZERO;
    for (our_limb, mod_limb) in self.as_mut().iter_mut().zip(modulus.as_ref()) {
      let new_limb;
      (new_limb, carry) = our_limb.carrying_add(*mod_limb, carry);
      our_limb.ct_assign(&new_limb, underflowed);
    }

    self
  }
}
impl<T: Sized + AsRef<[Limb]> + AsMut<[Limb]>> LimbHelpers for T {}

#[expect(private_bounds)]
pub(super) trait WideLimbs<Thin>: Clone + LimbHelpers {
  /// Calculate `self % denom`.
  ///
  /// Callers MUST NOT pass `denom = 0`.
  fn rem(self, denom: &Thin) -> Thin;
}

/// The required view over a collection of limbs to calculate the `c` coefficient.
///
/// Implementations MUST implement all functions in time constant to the value of the inputs,
/// except for the amount of limbs, unless otherwise stated. Implementations MUST NOT panic for any
/// input which the caller MAY pass.
#[expect(private_bounds)]
pub(crate) trait Limbs:
  Clone + AsRef<[Limb]> + AsMut<[Limb]> + CtEq + CtAssign + LimbHelpers
{
  /// A wider container capable of storing the product of any two values representable within this
  /// container.
  type Wide: WideLimbs<Self>;

  /// Calculate the GCD `d` of `self, other` (as `a, b`) and the coefficients such that
  /// `ua + vb = d`.
  ///
  /// Callers MUST ensure the inputs have the same amount of limbs. Callers MUST NOT pass
  /// `a = 0` or `b = 0`.
  ///
  /// Implementations MUST return values with the same amount of limbs as the inputs.
  #[expect(private_interfaces)]
  fn xgcd(self, other: Self) -> Xgcd<Self>;

  /// Calculate `self / denom` where `denom | self`.
  ///
  /// Callers MUST ensure the inputs have the same amount of limbs. Callers MUST NOT pass
  /// `denom = 0`.
  ///
  /// Implementations MUST return a value with the same amount of limbs as the numerator.
  fn div(self, denom: &Self) -> Self;

  /// Multiply two values modulo `modulus`.
  ///
  /// Callers MUST ensure the inputs have the same amount of limbs. Callers MUST NOT pass
  /// `modulus = 0`.
  ///
  /// Implementations MUST support any factors, not just those less than the modulus.
  /// Implementations MUST return a value with the same amount of limbs as the modulus.
  fn mul_mod(&self, other: &Self, modulus: &Self) -> Self {
    self.mul(other).rem(modulus)
  }

  /// Multiply two values into a wide value.
  fn mul(&self, other: &Self) -> Self::Wide;

  /// Square a value into a wide value.
  fn square(&self) -> Self::Wide {
    self.mul(self)
  }
}

/// Compose two positive definite binary quadratic forms.
///
/// This requires both forms be well-defined and of the same negative discriminant. Additionally,
/// we bound $\mathsf{gcd}(a1, a2, c1, c2, (b1 + b2) / 2, (b1 - b2) / 2) = 1$, which is trivially
/// satisfied when at least one form is primitive. Neither form is bound to be reduced however.
///
/// This function assumes:
/// - `floor(log_2(a1)) + 1 < AsRef::<[Limb]>::as_ref(&a1).len() * Limb::BITS`
/// - `floor(log_2(a2)) + 1 < AsRef::<[Limb]>::as_ref(&a2).len() * Limb::BITS`
/// - `AsRef::<[Limb]>::as_ref(&a1).len() == AsRef::<[Limb]>::as_ref(&a2).len()`
/// - `AsRef::<[Limb]>::as_ref(&a1).len() == AsRef::<[Limb]>::as_ref(&b2.1).len()`
/// - `AsRef::<[Limb]>::as_ref(&b1.1).len() == AsRef::<[Limb]>::as_ref(&b2.1).len()`
///
/// This returns the unreduced `a', b'` coefficients of the resulting form, with the following
/// bounds:
/// - $a' < 2^(floor(log_2(a1 * a2)) + 1)$
/// - $b' < 2^(1 + max(floor(log_2(|b2|)), floor(log_2(2 * a1 * a2))) + 1)$
pub(crate) fn add<U: Limbs>(
  a1: U,
  mut b1: I<U>,
  a2: U,
  b2: I<U>,
  c2: U::Wide,
) -> (U::Wide, I<U::Wide>) {
  /*
    `s = (b1 + b2) / 2`

    If the discriminant is odd, each `b` coefficient must be odd. If the discriminant is even, each
    `b` coefficient must be even. Accordingly, the `b` coefficients are congruent modulo `2`.

    The input is bounded such that these have an equivalent amount of limbs.
  */
  let s: I<U> = {
    let sign = sum_assign_half_of_two_numbers_congruent_mod_two(
      (b1.0, b1.1.as_mut()),
      (b2.0, b2.1.as_ref()),
    );
    (sign, b1.1)
  };

  let (d1, x2, y1, y2): (U, I<U>, I<U>, I<U>) = {
    /*
      This corresponds to step 2 of Algorithm 5.4.7 (the first Euclidean step). The described step
      short-circuits when `a1` is a factor of `a2`, but it's noted the general solution would work
      as well and that is solely an optimization. It's trivial to review it and confirm the
      short-circuit simply yields what the general solution would otherwise.
    */
    let (d, y1) = {
      /*
        `a1, a2` are non-zero for negative discriminants as with `b^2 - 4ac = -|delta|`, there
        would be no satisfaction if `a = 0`.
      */
      let xgcd = a2.clone().xgcd(a1.clone());
      (xgcd.d, xgcd.u)
    };

    /*
      This corresponds to step 3 (the second Euclidean step), which again has a described step
      which short-circuits when `d` is a factor of `s`. When `s` is non-zero, the general solution
      yields an equivalent result to the short-circuit. When `s` is zero, we do need to explicitly
      set `x_2 = 0, y_2 = -1, d_1 = d` however.

      `d` is non-zero as it's a factor of `a1, a2`.
    */
    let s_is_zero = {
      let mut s_is_zero = Limb::ZERO;
      for limb in s.1.as_ref() {
        s_is_zero |= *limb;
      }
      s_is_zero.is_zero()
    };

    /*
      If `s` is zero, set it to one so the following GCD call is well-defined.

      NOTE: This is probably extraneous. When one input is zero, most XGCD algorithms do still have
      a well-defined outputs, which we can probably bound to be the output required here without
      too many problems. At worst, the implementation provided by the underlying `Limbs`
      implementation would have to finess it as necessary.

      It's quite simple, and of negligible performance impact, to bound it here however and
      simplify the `Limbs` API accordingly.
    */
    let mut s_for_gcd = s.1.clone();
    s_for_gcd.as_mut()[0] |= Limb::from(u8::from(s_is_zero));
    let xgcd = s_for_gcd.xgcd(d.clone());

    let mut d1 = xgcd.d;
    // `d_1 = d` when `s = 0`
    d1.ct_assign(&d, s_is_zero);

    let mut x2 = xgcd.u;
    // If `s` was negative, correct the sign for its coefficient
    x2.0 ^= !s.0;
    // `x_2 = 0` when `s = 0`
    for x2_limb in x2.1.as_mut() {
      x2_limb.ct_assign(&Limb::ZERO, s_is_zero);
    }

    // `y_2 = -v`, hence why this negates the sign of `xgcd.v`
    let mut y2 = (!xgcd.v.0, xgcd.v.1);
    // `y_2 = -1` when `s = 0`
    y2.0.ct_assign(&Choice::FALSE, s_is_zero);
    y2.1.as_mut()[0].ct_assign(&Limb::ONE, s_is_zero);
    for y2_limb in &mut y2.1.as_mut()[1 ..] {
      y2_limb.ct_assign(&Limb::ZERO, s_is_zero);
    }

    (d1, x2, y1, y2)
  };

  /*
    `n = (b_1 - b_2) / 2 = ((b_1 + b_2) / 2) - b_2 = -(b_2 - s)`

    `diff_assign` assumes the result will fit within the output container. `(b1 - b2) / 2` will
    have bit-length at most equivalent to `max(b1, b2)`, so this assumption is upheld.

    We do return `b_2 - s`, not `-(b_2 - s)`, as the described algorithm says to. This is distinct
    from the more academic description preceding it which does define `n` as we do above, but in
    either case, the absolute value of the result is bounded as we needed.
  */
  let n: I<U> = {
    let mut b2 = (b2.0, b2.1.clone());
    let sign = diff_assign((b2.0, b2.1.as_mut()), (s.0, s.1.as_ref()));
    (sign, b2.1)
  };

  // `d1` is a factor of `d`, the greatest common factor of `a1, a2`, and therefore non-zero
  let v1: U = a1.div(&d1);
  let v2: U = a2.div(&d1);

  /*
    This computes `r` via the two parts of its equation, before taking their difference, entirely
    over the stated modulus. Note `mul_mod` is bound to be perfect, yet the `ct_neg_mod`, `sub_mod`
    helpers may yield `0 ..= modulus`, not `0 .. modulus`.

    As `modulus` is representable in `U`, this isn't an issue except at the very end as we expect
    `r` to be `0 ..= modulus`. Accordingly, at the very end, we do ensure the accuracy of this
    value.

    While this is silly, handling the edge case the value is the modulus at the very end avoids
    doing it at each step.
  */
  let r = {
    let r1 = y1.1.mul_mod(&y2.1, &v1).mul_mod(&n.1, &v1);
    let r1_is_negative = (!y1.0) ^ (!y2.0) ^ (!n.0);
    let (r1_was_zero, r1) = r1.ct_neg_mod(&v1, r1_is_negative);
    let r1_is_modulus = r1_was_zero & r1_is_negative;

    let r2 = x2.1.mul_mod(&c2.rem(&v1), &v1);
    let (r2_was_zero, r2) = r2.ct_neg_mod(&v1, !x2.0);
    let r2_is_zero = r2_was_zero & x2.0;

    let mut r_unreduced = r1.sub_mod(&r2, &v1);
    let r_unreduced_is_modulus = r1_is_modulus & r2_is_zero;
    for limb in r_unreduced.as_mut() {
      limb.ct_assign(&Limb::ZERO, r_unreduced_is_modulus);
    }
    r_unreduced
  };

  /*
    Because `U` can store `2 a`, `U::Wide` can store `4 a3`.

    `2 v2 r < 2 a3` as, by expansion, `2 v2 (_ % v1) < 2 v2 v1`.

    We then just have to prove `b2 < 2 a3`, which is trivial as `2 a3` is bounded to
    `U::Wide::BITS - 1` and `b2` is bounded to `U::BITS`, where
    `U::Wide::BITS >= (2 * U::BITS) - 1` (due to the requirement `U::Wide` is able to store any
    product of any values representable in `U`).

    This completes the proof `b3` is representable in `U::Wide` when `b2 >= 0`. When `b2 < 0`, the
    proof is trivial as `2 v2 r >= 0`, so the absolute value will be `<= max(|b2|, 2 v2 r)`.
  */
  let mut b3 = v2.mul(&r).double();
  let b3_is_negative = {
    let mut carry = Limb::ZERO;
    let mut borrow = Limb::ZERO;
    let mut b3_limbs = b3.as_mut().iter_mut();
    for (b3_limb, b2_limb) in
      (&mut b3_limbs).zip(b2.1.as_ref().iter().chain(core::iter::repeat(&Limb::ZERO)))
    {
      let if_add;
      (if_add, carry) = b3_limb.carrying_add(*b2_limb, carry);
      let if_sub;
      (if_sub, borrow) = b3_limb.borrowing_sub(*b2_limb, borrow);

      *b3_limb = Limb::ct_select(&if_sub, &if_add, b2.0);
    }

    // Clear the borrow if this was an addition, not a subtraction
    borrow.ct_assign(&Limb::ZERO, b2.0);

    // If the underflowed, negate `b3`
    let underflowed = !borrow.is_zero();
    let mut carry = Limb::from(u8::from(underflowed));
    let mask = Limb::ZERO.wrapping_sub(carry);
    for b3_limb in b3.as_mut() {
      let new_limb;
      (new_limb, carry) = ((*b3_limb) ^ mask).carrying_add(Limb::ZERO, carry);
      *b3_limb = new_limb;
    }

    /*
      This value is set to `b3_is_negative`. The resulting `b` will NOT be `-0` as if `b2 + 2 v2 r`
      underflowed, the absolute value of the result is non-zero (as `2 v2 r - |b2|` would only
      underflow if `|b2| > 2 v2 r`).
    */
    underflowed
  };

  let a3: U::Wide = v1.mul(&v2);

  (a3, (!b3_is_negative, b3))
}

/// Compose a positive definite binary quadratic form with itself.
///
/// This requires the form be well-defined and of the same negative _odd_ discriminant.
/// Additionally, we bound $\mathsf{gcd}(a, b, c) = 1$, which is trivially satisfied when the form
/// is primitive. The form is not bound to be reduced however.
///
/// This function assumes:
/// - `floor(log_2(a)) + 1 < AsRef::<[Limb]>::as_ref(&a).len() * Limb::BITS`
/// - `AsRef::<[Limb]>::as_ref(&a).len() == AsRef::<[Limb]>::as_ref(&b.1).len()`
///
/// This returns the unreduced `a', b'` coefficients of the resulting form, with the following
/// bounds:
/// - $a' < 2^(floor(log_2(a^2)) + 1)$
/// - $b' < 2^(1 + max(floor(log_2(|b|)), floor(log_2(2 * a^2))) + 1)$
//
// This is the above `add` function, specialized for the case the forms are the same. Comments
// which would be duplicated between the two functions are omitted.
pub(crate) fn double<U: Limbs>(a: U, b: I<U>, c: U::Wide) -> (U::Wide, I<U::Wide>) {
  // Because we bound that `delta` is _odd_, we know `s` is non-zero, as $b \cong delta \mod 2$
  let s = b.clone();
  let (d1, x2): (U, I<U>) = {
    // `d = a1, y1 = 0`
    let d = a.clone();

    let xgcd = s.1.xgcd(d);

    let d1 = xgcd.d;
    let mut x2 = xgcd.u;
    x2.0 ^= !s.0;

    (d1, x2)
  };

  let v1: U = a.div(&d1);

  let r = {
    // `r1 = 0` as `y1 = 0` (and as `n = 0`)

    let r2 = x2.1.mul_mod(&c.rem(&v1), &v1);
    let (r2_was_zero, mut r2) = r2.ct_neg_mod(&v1, !x2.0);
    let r2_is_zero = r2_was_zero & x2.0;

    // `r = 0 - r2 = -r2`
    let mut borrow = Limb::ZERO;
    for (mod_limb, r2_limb) in v1.as_ref().iter().zip(r2.as_mut()) {
      let new_limb;
      (new_limb, borrow) = mod_limb.borrowing_sub(*r2_limb, borrow);
      *r2_limb = <_>::ct_select(&new_limb, &Limb::ZERO, r2_is_zero);
    }
    r2
  };

  let mut b3 = v1.mul(&r).double();
  let b3_is_negative = {
    let mut carry = Limb::ZERO;
    let mut borrow = Limb::ZERO;
    let mut b3_limbs = b3.as_mut().iter_mut();
    for (b3_limb, b_limb) in
      (&mut b3_limbs).zip(b.1.as_ref().iter().chain(core::iter::repeat(&Limb::ZERO)))
    {
      let if_add;
      (if_add, carry) = b3_limb.carrying_add(*b_limb, carry);
      let if_sub;
      (if_sub, borrow) = b3_limb.borrowing_sub(*b_limb, borrow);

      *b3_limb = Limb::ct_select(&if_sub, &if_add, b.0);
    }

    borrow.ct_assign(&Limb::ZERO, b.0);

    let underflowed = !borrow.is_zero();
    let mut carry = Limb::from(u8::from(underflowed));
    let mask = Limb::ZERO.wrapping_sub(carry);
    for b3_limb in b3.as_mut() {
      let new_limb;
      (new_limb, carry) = ((*b3_limb) ^ mask).carrying_add(Limb::ZERO, carry);
      *b3_limb = new_limb;
    }

    underflowed
  };

  let a3: U::Wide = v1.square();

  (a3, (!b3_is_negative, b3))
}
