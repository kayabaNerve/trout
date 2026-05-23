//! A constant-time reduction algorithm.
//!
//! This is derived from Algorithm 1 of https://eprint.iacr.org/2022-466. Some typos have been
//! accounted for. Algorithm 2 is a restatement of Algorithm 1 in an iterative fashion and
//! accordingly may of more approximate structure to the following, yet this work was independently
//! derived from Algorithm 1.
//!
//! In order to be efficient, this does not always operate over the full amount of limbs of each
//! number. Instead, as the reduction occurs (and as the numbers shrink), the amount of limbs
//! operated over also reduce. This requires extensively arguing the bounds for inputs and the
//! outputs of each function. This is done via brief proofs written in comments within each
//! function.

use crypto_bigint::{Choice, CtEq, CtSelect, Zero, Limb, UintRef};

use super::Limbs;

/// Obtain the equivalent form `(a', b', c')` for which `a' <= c'`.
///
/// This assumes `c` has at least as many limbs as `a`.
///
/// This corresponds to step 2 of Algorithm 1.
#[inline(always)]
fn a_lte_c<L: Limbs>(a: &mut L, b_sign: &mut Choice, c: &mut L) {
  let limbs = <_ as AsRef<[Limb]>>::as_ref(c).len();
  let c_lt_a = c.lt(a, limbs);
  L::swap(a, c, limbs, c_lt_a);

  /*
    This line differs from the paper, whose described algorithm has a some typos (as further
    evidenced by the correctness proof transcribing line 6 as
    "[C - epsilon m B + m^2 A]" as "[C, - epsilon m B + A^2]").

    As this swaps `a, c`, and as it's known `(a, b, c) == (c, -b, a)`, we MUST negate `b` here
    if we performed a swap.
  */
  *b_sign ^= c_lt_a;
}

/// Reduce the `b` coefficient by at least one bit or until reduced.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `a <= c` (such as forms output of `a_lte_c`)
/// - `ceil(1 + log_2(|b|)) <= (limbs * Limb::BITS)` when `b_lte_a == false`
/// - `|b| < 2^b_bits_bound`
///
/// Yield an equivalent form `(a', b', c')` such that:
/// - `a' = a`
/// - `floor(log_2(|b'|)) <= floor(log_2(|b|)) - 1` if `|b| > 2 a` and
///   `(floor(log_2(|b|)) + 1) == b_bits_bound`, else `(a', b', c') = (a, b, c)`
/// - `|b'| <= a'` if `a < |b| <= 2 a`.
///
/// This corresponds to steps 3, 4, and 6 of Algorithm 1, except as a NOP if `b <= a` (in which
/// case the form is reduced, or reduced after normalizing the sign of `b`).
///
/// The steps of the reduction algorithm must run for however many iterations. As written, the
/// iterations will always occur until they don't occur. This is distinct in that this function
/// (representing a single iteration) only performs an operation _not_ if further iterations are
/// necessary, but if `(floor(log_2(|b|)) + 1) == b_bits_bound`. This is done as:
///
/// 1) It is still correct. This function, if called correctly, must be called from the current
///    bound to the minimal bound, the current bound decrementing by one bit with each call, as
///    this function is only guaranteed to reduce `|b|` by a single bit (if it's reduced at all).
///    Assuming the bound is properly decremented with each call, then we know `|b|` is within the
///    bound with each call, as the iteration is either unnecessary (the current bound exceeding
///    the actual `floor(log_2(|b|)) + 1`) or will be reduced by at least one (and therefore within
///    the next iteration's bound).
///
/// 2) It is faster to check if `(floor(log_2(|b|)) + 1) == b_bits_bound` than to calculate
///    `floor(log_2(|b|))`, even with how cheap that operation is. Finding the leading bit is an
///    operation of linear complexity, while checking if the highest bit within the bound is set is
///    of constant complexity (assuming the bound is public, allowing us to perform the retrieval
///    with a variable memory-access pattern). This optimization decreased the time of point
///    doubling by ~3.5%, implying this to optimize ~5% of reduction.
///
/// 3) If we always did the iterations which need to happen at the start, than being off-by-one
///    would be quite hard to detect as the last iterations are unlikely to actually be necessary.
///    This means `|b|` is likely below the bound for the entire duration of the algorithm, and the
///    bound being inaccurate may not be noticed. As this methodology intersperses the necessary
///    iterations with the unnecessary, `|b|` is worked with at the bound itself, which more
///    aggressively requires the accuracy of the bounds. This itself helps to ensure the bounds are
///    accurate.
#[inline(always)]
fn reduce_to_next_bit<L: Limbs>(
  a: &L,
  b: (&mut Choice, &mut UintRef),
  c: &mut L,
  b_lte_a: &mut Choice,
  limbs: usize,
  b_bits_bound: u32,
) {
  #[cfg(debug_assertions)]
  {
    debug_assert!(bool::from(a.lt(c, <_ as AsRef<[Limb]>>::as_ref(c).len())));
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(a).len());
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&b.1).len());
  }

  // Step 3 conditional

  /*
    Because this check is only valid when `a, b` fit within `limbs` limbs, short-circuit if we know
    know `b <= a`, in which case `limbs` may not be well-defined.
  */
  let b_gt_a = (!*b_lte_a) & {
    // If `a - b.1` has a borrow afterwards, then `b.1 > a`
    let mut a = a.clone();
    let a_ref = UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut a)[.. limbs]);
    !a_ref.borrowing_sub_assign(b.1, Limb::ZERO).is_zero()
  };
  /*
    Update `b_lte_a`.

    If `b_lte_a` is set, this will never unset it, as `b_gt_a` won't be set if `b_lte_a` was.
  */
  *b_lte_a = !b_gt_a;

  /*
    Only run this iteration if this specific bit of `b` is in fact set.

    This is a correct optimization, as we run for all bits regardless. It also is an optimization
    as it avoids having to determine the amount of bits in `b`, instead assuming it equal to the
    bound (or performing a NOP).

    This does slightly overload `b_gt_a` as a pseudo-`should_iterate`.
  */
  let b_gt_a = b_gt_a & Choice::from(b.1.bit_vartime(b_bits_bound.saturating_sub(1)) as u8);

  // Step 3 body, Step 4

  let log_2_m = {
    let a_bits = UintRef::new(&<_ as AsRef<[Limb]>>::as_ref(&a)[.. limbs]).bits();
    // This is correct per the check this bit, the highest possible, was actually set
    let b_bits = b_bits_bound;
    // This is only well-defined if `a_bits < b_bits`
    let log_2_m = b_bits.wrapping_sub(a_bits).wrapping_sub(1);
    // Set `m = 0` if `m` they have equal bit lengths or if `m` wouldn't be well-defined otherwise
    <_ as CtSelect>::ct_select(&0, &log_2_m, (!a_bits.ct_eq(&b_bits)) & b_gt_a)
  };

  // Step 6

  // When `b_gt_a = true`, `((1 << log_2_m) * a) < b`, so this will fit in `limbs` limbs
  let mut m_a = a.clone();
  let m_a = UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut m_a)[.. limbs]);
  m_a.shl_assign(log_2_m);

  /*
    The following does _not_ swap `c, a`, as we always perform any necessary swap during the next
    iteration's step 2 regardless. This means our `c` is updated to the paper's output `a`, and our
    `a` is left as-is.

    Note that in terms of this original paper which outputs `(a, b, c)`, this outputs `(c, b, a)`,
    which is not an equivalent form. The equivalent form would be `(c, -b, a)`. The paper is
    missing a negation on the output of its form, and once that's considered, this is equivalent.
  */

  // $\epsilon b == |b|$ since $\epsilon = \mathsf{sgn}(b)$
  /*
    Instead of calculating `- epsilon m b + m m a`, we calculate `m (-|b| + m a)` to reduce the
    bit-length of the addition within the parentheses. As `m a < b` when `a < b`, the evaluation
    of the parentheses is negative and has an absolute value `< |b|` (which fits in `limbs`
    limbs) whenever `b_gt_a == true`.

    When `b_gt_a = false`, `b_diff_m_a` is set to `0` so we may unconditionally calculate the new
    `c` coefficient as `c - m b_diff_m_a`.

    We simultaneously calculate $|b| - m a$ and $b - \epsilon 2 m a$ as we can merge their loops.
  */
  let mut b_diff_two_m_a_borrow = Limb::ZERO;
  let b_diff_m_a = {
    // This is a container of size `c` as we later operate on it with the bound the derivative is
    // `<= c`, which means this has to be large enough to contain a number `<= c`
    let mut b_diff_m_a = <L as Zero>::zero_like(&*c);
    {
      let b_diff_m_a =
        UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b_diff_m_a)[.. limbs]);

      let mut b_diff_m_a_borrow = Limb::ZERO;
      let mut two_m_a_carry = Limb::ZERO;
      for ((b_limb, m_a_limb), b_diff_m_a_limb) in
        b.1.iter_mut().zip(m_a.iter()).zip(b_diff_m_a.iter_mut())
      {
        let new_b_diff_m_a_limb;
        (new_b_diff_m_a_limb, b_diff_m_a_borrow) =
          b_limb.borrowing_sub(*m_a_limb, b_diff_m_a_borrow);
        *b_diff_m_a_limb = Limb::ct_select(&Limb::ZERO, &new_b_diff_m_a_limb, b_gt_a);

        let two_m_a_limb = (m_a_limb << 1) | two_m_a_carry;
        two_m_a_carry = m_a_limb >> const { Limb::BITS - 1 };

        /*
          `m a < |b| <= 2 m a`, so `||b| - 2 m a| < m a < |b|`, and `||b| - 2 m a|` will fit in any
          container `|b|` does.
        */
        let new_b_limb;
        (new_b_limb, b_diff_two_m_a_borrow) = b_limb.borrowing_sub(
          Limb::ct_select(&Limb::ZERO, &two_m_a_limb, b_gt_a),
          b_diff_two_m_a_borrow,
        );
        *b_limb = new_b_limb;
      }
    }
    b_diff_m_a
  };

  // Calculate the new `c` coefficient
  {
    /*
      We need to prove that `c >= (m b - m^2 a)`. We do so with the claim the output `c'` will be a
      positive integer, and therefore `c` MUST be greater than or equal to `m b - m^2 a` (when
      `b_gt_a = true`), as else `c'` would be negative.

      We know each intermediate form is equivalent to the input form, and therefore as for input
      `(a, b, c)` satisfying `b^2 - (4 a c) = delta`, we have `b'^2 - (4 a' c') = delta`. As
      `delta < 0`, and `b^2 >= 0`, `4 a' c'` MUST be a positive number. As our algorithm sets
      `a' = a` where `a` is positive, `c'` must be positive as well.

      Because `c` is greater than or equal to `m b - m^2 a`, it will fit within a container which
      fits `c`, where `b_diff_m_a` is a container of size equal to `c`'s container (making this
      `shl` call well-defined).
    */
    let mut m_b_diff_m_square_a = b_diff_m_a;
    UintRef::new_mut(<_ as AsMut<[Limb]>>::as_mut(&mut m_b_diff_m_square_a)).shl_assign(log_2_m);
    let m_b_diff_m_square_a = m_b_diff_m_square_a;

    // This subtraction is well-defined as `c >= m_b_diff_m_square_a` when `b_gt_a = true`
    let mut borrow = Limb::ZERO;
    for (c_limb, m_b_diff_m_square_a_limb) in <_ as AsMut<[Limb]>>::as_mut(c)
      .iter_mut()
      .zip(<_ as AsRef<[Limb]>>::as_ref(&m_b_diff_m_square_a))
    {
      // When `b_gt_a = false`, `m_b_diff_m_square_a_limb = 0`, effecting a NOP
      let new_limb;
      (new_limb, borrow) = c_limb.borrowing_sub(*m_b_diff_m_square_a_limb, borrow);
      *c_limb = new_limb;
    }
  }

  // Finish calculating the new `b` coefficient, handling if it underflowed
  {
    let borrow = b_diff_two_m_a_borrow;
    // If this underflowed (`2 m a > |b|`) and `borrow != 0`, apply the logical NOT to take the
    // absolute value
    let mut overflow_carry = Limb::ONE & borrow;
    // If `2 m a > |b|`, flip the sign of the result
    // $overflow_carry \in {0, 1}$, making this cast safe, and is `1` if `2 m a > |b|`
    #[expect(clippy::as_conversions, clippy::cast_possible_truncation)]
    {
      *b.0 ^= Choice::from(overflow_carry.0 as u8);
    }
    for b_limb in b.1.iter_mut() {
      *b_limb ^= borrow;
      let new_limb;
      (new_limb, overflow_carry) = b_limb.carrying_add(Limb::ZERO, overflow_carry);
      *b_limb = new_limb;
    }
  }
}

/// Normalize an almost-reduced element.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `|b| <= a <= c`
///
/// Yield the reduced equivalent form `(a', b', c')` such that:
/// - `|b'| <= a' <= c'`
/// - `b' >= 0` if `(|b'| == a') || (a' == c')`
///
/// This is intended to correspond to steps 2 and 5 of Algorithm 1.
#[inline(always)]
fn normalize<L: Limbs>(mut a: L, mut b: (Choice, L), mut c: L) -> (L, (Choice, L), L) {
  a_lte_c(&mut a, &mut b.0, &mut c);
  // Set `b'` to be positive if `|b| == a` or `a == c`, or if `b == 0`
  // (in order to not return `-0`)
  b.0 |= b.1.ct_eq(&a) | a.ct_eq(&c) | b.1.is_zero();
  (a, b, c)
}

/// Calculate `c` such that `b^2 - 4ac = delta`.
///
/// The following bounds are present:
/// - `delta < 0`
/// - `ceil(log_2(a)) <= log_2_a_bound`
/// - `|b| < 2 a`
/// - There is an integer solution for `c` in `b^2 - 4 a c = delta`.
/// - `(a - delta) < 2^(<L as AsRef::<[Limb]>>::as_ref(&b.1).len() * Limb::BITS)`
///
/// `delta` is specified via its absolute value in `negative_discriminant_abs`.
#[inline(always)]
pub(crate) fn c<L: Limbs>(a: &L, b: &(Choice, L), negative_discriminant_abs: &L) -> L {
  /*
    We bound our input `b` to be `< 2 a`, so at most `b^2 = (2 (a - 1))^2`, ensuring
    `b^2 < (2 a)^2` (or rather that `b^2 < 4 a^2`). As `(b^2 - delta) / (4 a) = c`, where
    `b^2 < (4 a^2)`, we know `c < ((4 a^2 - delta) / (4 a))` (or rather that
    `c < a - (delta / 4a)`).

    This ensures we can calculate `c` in any container able to fit `a - delta`, where the
    container of `b` is so bounded.
  */

  let (b_lo, b_hi) = b.1.widening_square();

  // Subtracting the negative discriminant is equivalent to adding its absolute value
  let (four_ac_lo, carry) = b_lo.carrying_add(negative_discriminant_abs, Limb::ZERO);
  let (four_ac_hi, carry) = b_hi.carrying_add(&<L as Zero>::zero_like(a), carry);
  debug_assert_eq!(carry, Limb::ZERO);

  let mut ac_lo = four_ac_lo.unbounded_shr_vartime(2);
  ac_lo.set_bit_vartime(ac_lo.bits_precision() - 2, four_ac_hi.bit_vartime(0));
  ac_lo.set_bit_vartime(ac_lo.bits_precision() - 1, four_ac_hi.bit_vartime(1));
  let ac_hi = four_ac_hi.unbounded_shr_vartime(2);
  let ac = (ac_lo, ac_hi);

  L::wrapping_div(ac, a)
}

/// Partially reduce a positive definite binary quadratic form.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `ceil(log_2(a)) <= log_2_a_bound`
/// - `|b| < 2 a`
/// - There is an integer solution for `c` in `b^2 - 4 a c = delta`.
/// - `ceil(log_2_a_bound / Limb::BITS) <= <L as AsRef::<[Limb]>>::as_ref(&a).len())`
/// - `<L as AsRef::<[Limb]>>::as_ref(&a).len()) <= <L as AsRef::<[Limb]>>::as_ref(&b.1).len())`
/// - `(a - delta) < 2^(<L as AsRef::<[Limb]>>::as_ref(&b.1).len() * Limb::BITS)`
///
/// Yield an equivalent form `(a', b', c')` such that:
/// - `a' <= c'`
/// - `b'^2 <= |delta|`
/// - `(a', b', c')` is reduced or `b' > a'`
///
/// As composition is presumably programmed to compose `b`-bit-length numbers, where composition
/// outputs `2 * b`-bit-length numbers, this function intends to solely perform the necessary
/// reduction such that the numbers are once again of `b`-bit-length (and able to be composed
/// again). While these forms are not reduced, they may still usable for composition _without_
/// performing a full reduction (which would take roughly twice as long). This allows deferring a
/// full reduction until one _needs_ a reduced form.
///
/// This third bound on the output, `(a', b', c')` is reduced or `b' > a'`, is critical as it
/// enables the following corollary: `a'^2 < |delta|`.
///
/// `b.0, b'.0` are `true` if the value is _positive_.
///
/// `delta` is bound to be negative and specified via its absolute value in
/// `negative_discriminant_abs`.
#[expect(private_bounds)]
#[inline(always)]
pub(crate) fn partial_reduce<L: Limbs>(
  log_2_a_bound: u32,
  mut a: L,
  mut b: (Choice, L),
  negative_discriminant_abs: &L,
) -> (L, (Choice, L), L) {
  #[cfg(debug_assertions)]
  {
    debug_assert!(a.bits() <= log_2_a_bound);
    debug_assert!(
      usize::try_from(log_2_a_bound.div_ceil(Limb::BITS)).unwrap() <=
        <_ as AsRef::<[Limb]>>::as_ref(&a).len()
    );
    debug_assert_eq!(
      <_ as AsRef::<[Limb]>>::as_ref(&a).len(),
      <_ as AsRef::<[Limb]>>::as_ref(&b.1).len()
    );

    let limbs = <_ as AsRef<[Limb]>>::as_ref(&a).len();
    debug_assert!(bool::from(b.1.lt(&a.clone().double(limbs), limbs)));
  }

  let mut c = c(&a, &b, negative_discriminant_abs);

  // From the bound that `b < 2 a`
  let log_2_b_bound = log_2_a_bound + 1;
  let discriminant_bits = negative_discriminant_abs.bits_vartime();
  let original_limbs = usize::try_from(log_2_b_bound.div_ceil(Limb::BITS)).unwrap();

  /*
    Iterate from our bound on `b` to a `b'` which by bit-length, would satisfy `b'^2 < |delta|`.
    Each iteration will reduce the bit length of `b` by at least `1`, until `b <= a` and it is
    reduced.
  */
  {
    let mut limbs = original_limbs;
    let mut progress_in_limb = Limb::BITS - (log_2_b_bound % Limb::BITS);
    let (b_sign, mut b_value) =
      (&mut b.0, UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b.1)[.. limbs]));
    let mut b_lte_a = Choice::FALSE;
    for bits in ((discriminant_bits / 2) ..= log_2_b_bound).rev() {
      a_lte_c(&mut a, b_sign, &mut c);

      reduce_to_next_bit(&a, (b_sign, b_value), &mut c, &mut b_lte_a, limbs, bits);

      /*
        `reduce_to_next_bit` is documented to need limbs corresponding to one extra bit, which is
        as `ceil(log_2(b)) == ceil(log_2(a))` is a possible input and the function must then
        calculate `2 m a`.

        We provide one additional bit here as for a value `b <= a`, this will only be noticed on
        the iteration _after_ the condition becomes true, so we need to defer when we move to the
        smaller amount of limbs until after this later iteration.
      */
      if progress_in_limb == const { 2 + Limb::BITS } {
        progress_in_limb = 2;
        limbs -= 1;
        b_value = b_value.leading_mut(limbs);
      }
      progress_in_limb += 1;
    }
  }

  // Ensure `a' <= c'`, as we bound our output
  a_lte_c(&mut a, &mut b.0, &mut c);

  #[cfg(debug_assertions)]
  {
    debug_assert!(b.1.bits() <= discriminant_bits.div_ceil(2));
  }

  (a, b, c)
}

/// Reduce an element.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `ceil(log_2(a)) <= log_2_a_bound`
/// - `|b| < 2 a`
/// - There is an integer solution for `c` in `b^2 - 4 a c = delta`.
/// - `ceil(log_2_a_bound / Limb::BITS) <= <L as AsRef::<[Limb]>>::as_ref(&a).len())`
/// - `<L as AsRef::<[Limb]>>::as_ref(&a).len()) <= <L as AsRef::<[Limb]>>::as_ref(&b.1).len())`
/// - `(a - delta) < 2^(<L as AsRef::<[Limb]>>::as_ref(&b.1).len() * Limb::BITS)`
///
/// Yield the reduced equivalent form `(a', b', c')` such that:
/// - `|b'| <= a' <= c'`
/// - `b' >= 0` if `(|b'| == a') || (a' == c')`
///
/// `b.0, b'.0` are `true` if the value is _positive_.
///
/// `delta` is bound to be negative and specified via its absolute value in
/// `negative_discriminant_abs`.
//
// As this function is a derivative of `partial_reduce`, it lacks internal comments which would be
// identical between the two.
#[expect(private_bounds)]
#[inline(always)]
pub(crate) fn reduce<L: Limbs>(
  log_2_a_bound: u32,
  mut a: L,
  mut b: (Choice, L),
  negative_discriminant_abs: &L,
) -> (L, (Choice, L), L) {
  #[cfg(debug_assertions)]
  {
    debug_assert!(a.bits() <= log_2_a_bound);
    debug_assert!(
      usize::try_from(log_2_a_bound.div_ceil(Limb::BITS)).unwrap() <=
        <_ as AsRef::<[Limb]>>::as_ref(&a).len()
    );
    debug_assert_eq!(
      <_ as AsRef::<[Limb]>>::as_ref(&a).len(),
      <_ as AsRef::<[Limb]>>::as_ref(&b.1).len()
    );

    let limbs = <_ as AsRef<[Limb]>>::as_ref(&a).len();
    debug_assert!(bool::from(b.1.lt(&a.clone().double(limbs), limbs)));
  }

  let mut c = c(&a, &b, negative_discriminant_abs);

  let log_2_b_bound = log_2_a_bound + 1;
  let original_limbs = usize::try_from(log_2_b_bound.div_ceil(Limb::BITS)).unwrap();

  {
    let mut limbs = original_limbs;
    let mut progress_in_limb = Limb::BITS - (log_2_b_bound % Limb::BITS);
    let (b_sign, mut b_value) =
      (&mut b.0, UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b.1)[.. limbs]));
    let mut b_lte_a = Choice::FALSE;
    for bits in (0 ..= log_2_b_bound).rev() {
      a_lte_c(&mut a, b_sign, &mut c);

      reduce_to_next_bit(&a, (b_sign, b_value), &mut c, &mut b_lte_a, limbs, bits);

      if progress_in_limb == const { 2 + Limb::BITS } {
        progress_in_limb = 2;
        limbs -= 1;
        b_value = b_value.leading_mut(limbs);
      }
      progress_in_limb += 1;
    }
  }

  a_lte_c(&mut a, &mut b.0, &mut c);
  let (a, b, c) = normalize(a, b, c);

  #[cfg(debug_assertions)]
  {
    debug_assert!(bool::from(
      b.1.lt(&a, AsRef::<[Limb]>::as_ref(&a).len()) | b.1.eq(&a, AsRef::<[Limb]>::as_ref(&a).len())
    ));
    debug_assert!(bool::from(
      a.lt(&c, AsRef::<[Limb]>::as_ref(&a).len()) | a.lt(&c, AsRef::<[Limb]>::as_ref(&a).len())
    ));
  }

  (a, b, c)
}
