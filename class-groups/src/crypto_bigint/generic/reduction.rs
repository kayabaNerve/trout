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

use crypto_bigint::{Choice, CtEq, CtGt, CtSelect, Zero, Limb, UintRef};

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

/// If `reduce_to_next_bit` should actually apply, except possibly incorrect.
///
/// This MAY yield `false` even when one final iteration should be ran, hence `except_final`. It is
/// correct for all but the final iteration.
///
/// This simplifies `|b| > a` to `floor(log_2(|b|)) > floor(log_2(a))`, which is true whenever
/// `|b| >= 2a`. See `should_reduce_to_next_bit_final` for why this is sufficient for all but the
/// last iteration.
///
/// This is optimized by only indicating the reduction algorithm should be run when
/// `(floor(log_2(|b|)) + 1) == b_bits_bound` _not_ always if `|b| >= 2a`. This is done as:
///
/// 1) It is still correct. `reduce_to_next_bit`, if called correctly, must be called from the
///    current bound to the minimal bound, the current bound decrementing by one bit with each call,
///    as `reduce_to_next_bit is only guaranteed to reduce `|b|` by a single bit (until `b` is
///    reduced). Assuming the bound is properly decremented with each call, then we know `|b|` is
///    within the bound for each call, as the iteration is either unnecessary (the current bound
///    exceeding the actual `floor(log_2(|b|)) + 1`) or will be reduced by at least one bit (and
///    therefore within the next iteration's bound) if not already reduced.
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
///
/// This function assumes `a_bits = floor(log_2(a)) + 1` and
/// `b_bits_bound >= floor(log_2(|b|)) + 1` when `b_lte_a == false`. This function will update
/// `b_lte_a`, but may be inaccurately set upon reaching the final necessary iteration.
#[inline(always)]
fn should_reduce_to_next_bit_except_final(
  b: (&mut Choice, &mut UintRef),
  b_needs_negation: Choice,
  b_lte_a: &mut Choice,
  a_bits: u32,
  b_bits_bound: u32,
) -> Choice {
  // Because this check is only valid `b_lte_a == false`, short-circuit if `b_lte_a == false`
  let b_gt_a = (!*b_lte_a) & b_bits_bound.ct_gt(&a_bits);

  /*
    Update `b_lte_a`.

    If `b_lte_a` is set, this will never unset it, as `b_gt_a` won't be set if `b_lte_a` was.
  */
  *b_lte_a = !b_gt_a;

  // Only run this iteration if this specific bit of `b` is in fact set
  b_gt_a &
    Choice::from(b.1.bit_vartime(b_bits_bound.saturating_sub(1)) as u8).ct_eq(&!b_needs_negation)
}

/// If `reduce_to_next_bit` should actually apply.
///
/// This uses an exact determination for if the function should apply, which is only necessary when
/// `floor(log_2(|b|)) == floor(log_2(a))`. However, in this case, `b <= 2 a`. The paper itself
/// establishes the bound the algorithm will run for at most two more iterations in this case, yet
/// a tighter bound of just one more iteration is possible. This is as the `b == 2a` case will
/// resolved with `b' = 0`, while the case `a < b < 2a` will result in `b' < a`.
///
/// That's why this is 'final', as while it works all of the time, it should only be used for one
/// final iteration.
///
/// This function assumes:
/// - `limbs == <_ as AsRef<[Limb]>>(b.1).len()`
/// - `limbs <= <_ as AsRef<[Limb]>>(a).len()`
/// - $a, b <= 2^{limbs * Limb::BITS}$
///
/// Comments within this function which would be duplicated with
/// `should_reduce_to_next_bit_except_final` are omitted.
#[inline(always)]
fn should_reduce_to_next_bit_final<L: Limbs>(
  a: &L,
  b: (&mut Choice, &mut UintRef),
  limbs: usize,
) -> Choice {
  // If `a - b.1` has a borrow afterwards, then `b.1 > a`
  let mut a = a.clone();
  let a_ref = UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut a)[.. limbs]);
  !a_ref.borrowing_sub_assign(b.1, Limb::ZERO).is_zero()
}

fn negate_b(b: (&mut Choice, &mut UintRef), b_needs_negation: Choice) {
  *b.0 ^= b_needs_negation;
  // If this needs negation, apply the logical NOT and add `1` to take the absolute value
  let mut overflow_carry = Limb::from(u8::from(b_needs_negation));
  let mask = Limb::ZERO.wrapping_sub(overflow_carry);
  for b_limb in b.1.iter_mut() {
    let new_limb;
    (new_limb, overflow_carry) = (*b_limb ^ mask).carrying_add(Limb::ZERO, overflow_carry);
    *b_limb = new_limb;
  }
}

/// Reduce the `b` coefficient by at least one bit or until reduced.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `a <= c` (such as forms output of `a_lte_c`)
/// - `limbs <= <_ as AsRef<[Limb]>>(a).len()`
/// - `limbs <= <_ as AsRef<[Limb]>>(b.1).len()`
/// - The variable `c` does in fact contain the full representation of the `c` coefficient.
///
/// We require the following bounds when `should_reduce == true`:
/// - `a < b`
/// - `a_bits = floor(log_2(a)) + 1`
/// - `b_bits = floor(log_2(|b|)) + 1`
/// - `1 + b_bits <= (limbs * Limb::BITS)`
///
/// Yield an equivalent form `(a', b', c')` such that:
/// - `a' = a`
/// - `floor(log_2(|b'|)) <= floor(log_2(|b|)) - 1` if `|b| > 2 a` and `should_reduce == true`,
///   else `(a', b', c') = (a, b, c)`
/// - `|b'| <= a'` if `a < |b| <= 2 a` and `should_reduce == true`.
///
/// This corresponds to steps 3, 4, and 6 of Algorithm 1, except as a NOP if
/// `should_reduce == false` (`b <= a`) (in which case the form is reduced, or reduced after
/// normalizing the sign of `b`).
#[inline(always)]
fn reduce_to_next_bit<L: Limbs>(
  a: &L,
  b: (&mut Choice, &mut UintRef),
  b_needs_negation: &mut Choice,
  c: &mut L,
  should_reduce: Choice,
  limbs: usize,
  a_bits: u32,
  b_bits: u32,
) {
  #[cfg(debug_assertions)]
  {
    debug_assert!(bool::from(a.lt(c, <_ as AsRef<[Limb]>>::as_ref(c).len())));
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(a).len());
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&b.1).len());
  }

  // Calculate `m` (the body of step 3's branch, step 4)
  let log_2_m = {
    // This is only well-defined if `a_bits < b_bits`
    let log_2_m = b_bits.wrapping_sub(a_bits).wrapping_sub(1);
    // Set `m = 0` if `m` they have equal bit lengths or if `m` wouldn't be well-defined otherwise
    <_ as CtSelect>::ct_select(&0, &log_2_m, (!a_bits.ct_eq(&b_bits)) & should_reduce)
  };

  // Step 6


  // This is a container of size `c` as we later operate on it with the bound the derivative is
  // `<= c`, which means this has to be large enough to contain a number `<= c`
  let mut m_a = <L as Zero>::zero_like(&*c);
  // When `should_reduce = true`, `((1 << log_2_m) * a) < b`, so this will fit in `limbs` limbs
  {
    let m_a = UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut m_a)[.. limbs]);
    m_a.copy_from_slice(&a.as_ref()[.. limbs]);
    m_a.shl_assign(log_2_m);
  }
  let m_a = UintRef::new_mut(<_ as AsMut<[Limb]>>::as_mut(&mut m_a));

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
    of the parentheses is negative and has an absolute value `< |b|` (which fits in `limbs` limbs)
    whenever `should_reduce == true`.

    When `should_reduce == false`, `b_diff_m_a` is set to `0` so we may unconditionally calculate
    the new `c` coefficient as `c - m b_diff_m_a`.

    We simultaneously calculate $|b| - m a$ and $b - \epsilon 2 m a$ as we can merge their loops.
    While the resulting code is of non-trivially greater complexity, it saves ~8% of the time to
    execute.

    Note $b - \epsilon 2 m a$ may underflow, causing `b'` to have a distinct sign from `b`. In
    order to ensure the variable `b.1` remains the absolute value, this would require the logical
    NOT operator combined with a carrying addition of `1` _after_ calculating $b - \epsilon 2 m a$.
    To avoid another loop, we instead defer performing the negation to the next iteration's
    instance of _this_ loop, reducing the amount of times we introduce flow control/branching, via
    the `b_needs_negation` variable. Note the caller must handle `b_needs_negation` when shifting
    `b`'s limb boundaries.
  */
  {
    {
      *b.0 ^= *b_needs_negation;
      let b_negation_carry = Limb::from(u8::from(*b_needs_negation));
      let b_negation_mask = Limb::ZERO.wrapping_sub(b_negation_carry);

      let mut b_diff_m_a_carry = Limb::ZERO;

      let mut two_m_a_carry = Limb::ZERO;
      /*
        We express `b - 2 m a` as `b + -(2 m a)`, where the negation requires a carry of `1`
        (hence why this is initialized to `1` when `should_reduce == true`). We simultaneously
        apply the deferred negation to `b`, hence why we also sum `b_negation_carry`.
      */
      let mut b_diff_two_m_a_carry = Limb::from(u8::from(should_reduce)).wrapping_add(b_negation_carry);

      for (b_limb, m_a_limb) in b.1.iter_mut().zip(m_a.iter_mut()) {
        /*
          Set `b' = b - 2 m a`, while simultaneously negating `b_limb` (if necessary).

          Negating `b'` is expressed as the logical NOT combined with a carrying addition of `1`.
          This is incompatible with needing to perform a borrowing subtraction of `2 m a`. Instead,
          we rewrite it as `b + -(2 m a)`, where `2 m a`'s negation can be expressed with a
          carrying addition. This means all three aspects (negating `b` if necessary, negating
          `2 m a`, and summing `b, 2 m a`) can be so expressed and done simultaneously.
        */
        {
          let two_m_a_limb = ((*m_a_limb) << 1) | two_m_a_carry;
          two_m_a_carry = (*m_a_limb) >> const { Limb::BITS - 1 };

          /*
            `floor(log_2(|b|)) = floor(log_2(2 m a))`, so their difference `|b'|` has the property
            `floor(log_2(|b'|)) < floor(log_2(|b|))`. Therefore, `|b'|` will fit in any container
            which fits `|b|`.
          */
          let new_b_limb;
          (new_b_limb, b_diff_two_m_a_carry) = ((*b_limb) ^ b_negation_mask).carrying_add(
            Limb::ct_select(&Limb::ZERO, &(two_m_a_limb ^ Limb::MAX), should_reduce),
            b_diff_two_m_a_carry,
          );
          *b_limb = new_b_limb;
        }

        /*
          Calculate `b_diff_m_a` as `b' + m a` (where `b' = b - 2 m a`).

          This writes `b_diff_m_a` directly into `m_a`, as we have no further use for `m_a`.
        */
        {
          let new_b_diff_m_a_limb;
          (new_b_diff_m_a_limb, b_diff_m_a_carry) =
            (*b_limb).carrying_add(*m_a_limb, b_diff_m_a_carry);
          *m_a_limb = Limb::ct_select(&Limb::ZERO, &new_b_diff_m_a_limb, should_reduce);
        }
      }

      /*
        Finish calculating `b'`, handling if `b < 2 m a`.

        Because we expressed `b'` as `b + -(2 m a)`, there is _no_ carry if `2 m a > b`. This means
        `b'` needs negation if there was _no_ carry.
      */
      *b_needs_negation = should_reduce & b_diff_two_m_a_carry.ct_eq(&Limb::ZERO);
    }
  }
  let b_diff_m_a = m_a;

  // Calculate the new `c` coefficient
  {
    /*
      We need to prove that `c >= (m b - m^2 a)`. We do so with the claim the output `c'` will be a
      positive integer, and therefore `c` MUST be greater than or equal to `m b - m^2 a` (when
      `should_reduce == true`), as else `c'` would be negative.

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

    // This subtraction is well-defined as `c >= m_b_diff_m_square_a` when `should_reduce == true`
    let mut borrow = Limb::ZERO;
    for (c_limb, m_b_diff_m_square_a_limb) in <_ as AsMut<[Limb]>>::as_mut(c)
      .iter_mut()
      .zip(<_ as AsRef<[Limb]>>::as_ref(&m_b_diff_m_square_a))
    {
      // When `should_reduce == false`, `m_b_diff_m_square_a_limb = 0`, effecting a NOP
      let new_limb;
      (new_limb, borrow) = c_limb.borrowing_sub(*m_b_diff_m_square_a_limb, borrow);
      *c_limb = new_limb;
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
fn normalize<L: Limbs>(a: L, mut b: (Choice, L), c: L) -> (L, (Choice, L), L) {
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

    TODO: The size of this is weird. It's... `4 + log_2(|delta|) + 1`?
  */

  let (b_lo, b_hi) = b.1.widening_square();

  // Subtracting the negative discriminant is equivalent to adding its absolute value
  let mut four_ac_lo = b_lo;
  let carry = UintRef::new_mut(<_ as AsMut<[Limb]>>::as_mut(&mut four_ac_lo))
    .carrying_add_assign_slice(negative_discriminant_abs.as_ref(), Limb::ZERO);
  let mut four_ac_hi = b_hi;
  let carry =
    UintRef::new_mut(<_ as AsMut<[Limb]>>::as_mut(&mut four_ac_hi)).add_assign_limb(carry);
  debug_assert_eq!(carry, Limb::ZERO);

  let mut ac_lo = four_ac_lo.unbounded_shr_vartime(2);
  ac_lo.set_bit_vartime(ac_lo.bits_precision() - 2, four_ac_hi.bit_vartime(0));
  ac_lo.set_bit_vartime(ac_lo.bits_precision() - 1, four_ac_hi.bit_vartime(1));
  let ac_hi = four_ac_hi.unbounded_shr_vartime(2);
  let ac = (ac_lo, ac_hi);

  L::wrapping_div(ac, a)
}

/// Reduce an element until either its reduced or $|b| < 2^{lower_bound}$.
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
/// - `(a', b', c')` is reduced or $|b| < 2^{lower_bound}$.
/// - `(a', b', c')` is reduced or `b' > a'`
///
/// `b.0, b'.0` are `true` if the value is _positive_.
///
/// `delta` is bound to be negative and specified via its absolute value in
/// `negative_discriminant_abs`.
#[inline(always)]
pub(crate) fn reduce_to_lower_bound<L: Limbs>(
  log_2_a_bound: u32,
  mut a: L,
  mut b: (Choice, L),
  negative_discriminant_abs: &L,
  lower_bound: u32,
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
  let original_limbs = usize::try_from(log_2_b_bound.div_ceil(Limb::BITS)).unwrap();

  /*
    Iterate from our bound on `b` to a `b'` which by bit-length, would satisfy `b'^2 < |delta|`.
    Each iteration will reduce the bit length of `b` by at least `1`, until `b <= a` and it is
    reduced (if given sufficient iterations to reach that point).
  */
  {
    let (b_sign, mut b_value) =
      (&mut b.0, UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b.1)[.. original_limbs]));
    let mut b_lte_a = Choice::FALSE;
    let mut b_needs_negation = Choice::FALSE;

    let mut limbs = original_limbs;
    /*
      `reduce_to_next_bit` is documented to need limbs corresponding to one extra bit, which is
      as `ceil(log_2(b)) == ceil(log_2(a))` is a possible input and the function must then
      calculate `2 m a`.

      We provide one additional bit here as for a value `b <= a`, this will only be noticed on
      the iteration _after_ the condition becomes true, so we need to defer when we move to the
      smaller amount of limbs until after this later iteration.
    */
    const DECREASE_LIMBS_AT: u32 = 2 + Limb::BITS;

    // `RangeInclusive` doesn't implement `FixedSizeIterator`, so we use a `Range` instead
    let mut bits = ((lower_bound + 1) .. (log_2_b_bound + 1)).rev();

    // Handle the partial limb we inherently have by the bound not perfectly aligning to limbs
    {
      let progress_in_limb = Limb::BITS - (log_2_b_bound % Limb::BITS);
      for bits in (&mut bits).take((DECREASE_LIMBS_AT - progress_in_limb) as usize) {
        a_lte_c(&mut a, b_sign, &mut c);
        let a_bits = a.bits();
        let should_reduce = should_reduce_to_next_bit_except_final(
          (b_sign, b_value),
          b_needs_negation,
          &mut b_lte_a,
          a_bits,
          bits,
        );
        reduce_to_next_bit(
          &a,
          (b_sign, b_value),
          &mut b_needs_negation,
          &mut c,
          should_reduce,
          limbs,
          a_bits,
          bits,
        );
      }

      // Negate `b` if necessary, before crossing the limb boundary
      negate_b((b_sign, b_value), b_needs_negation);
      b_needs_negation = Choice::FALSE;

      limbs -= 1;
      b_value = b_value.leading_mut(limbs);
    }

    /*
      Handle each remaining limb.

      While we could use a single loop for both the partial limb and the full limbs, that would
      have structure approximate to:

      ```
      for bit {
        reduce_to_next_bit();
        if limb {
          limbs -= 1;
        }
      }
      ```

      and place a branch within every single loop body. This achieves a straight-line, other than
      the loops' conditionals themselves (which the compiler appears to handle better, possibly as
      we may use the constant `DECREASE_LIMBS_AT` for how many steps this inner loop takes).

      `bits.len() != 0` is used as `bits.is_empty()` (`FixedSizeIterator::is_empty`) is
      experimental.
    */
    while bits.len() != 0 {
      for bits in (&mut bits).take(DECREASE_LIMBS_AT as usize) {
        a_lte_c(&mut a, b_sign, &mut c);
        let a_bits = a.bits();
        let should_reduce = should_reduce_to_next_bit_except_final(
          (b_sign, b_value),
          b_needs_negation,
          &mut b_lte_a,
          a_bits,
          bits,
        );
        reduce_to_next_bit(
          &a,
          (b_sign, b_value),
          &mut b_needs_negation,
          &mut c,
          should_reduce,
          limbs,
          a_bits,
          bits,
        );
      }

      negate_b((b_sign, b_value), b_needs_negation);
      b_needs_negation = Choice::FALSE;

      limbs -= 1;
      b_value = b_value.leading_mut(limbs);
    }

    /*
      We apply the final reduction with a full width as we don't know when the above iterations
      stopped, nor how far the number has been truncated since.
    */
    {
      let (b_sign, b_value) = (
        &mut b.0,
        UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b.1)[.. original_limbs]),
      );

      a_lte_c(&mut a, b_sign, &mut c);
      let a_bits = a.bits();
      let b_bits = b_value.bits();
      let should_reduce = should_reduce_to_next_bit_final(&a, (b_sign, b_value), original_limbs);
      reduce_to_next_bit(
        &a,
        (b_sign, b_value),
        &mut b_needs_negation,
        &mut c,
        should_reduce,
        original_limbs,
        a_bits,
        b_bits,
      );

      negate_b((b_sign, b_value), b_needs_negation);
    }
  }

  (a, b, c)
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
/// This second bound on the output, `(a', b', c')` is reduced or `b' > a'`, is critical as it
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
  a: L,
  b: (Choice, L),
  negative_discriminant_abs: &L,
) -> (L, (Choice, L), L) {
  let discriminant_bits = negative_discriminant_abs.bits_vartime();
  let sqrt_discriminant_bits = discriminant_bits.div_ceil(2);
  let (mut a, mut b, mut c) = reduce_to_lower_bound(
    log_2_a_bound,
    a,
    b,
    negative_discriminant_abs,
    sqrt_discriminant_bits - 1,
  );

  // This is needed to ensure our second bound, "`(a', b', c')` is reduced or `b' > a'`"
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
#[expect(private_bounds)]
#[inline(always)]
pub(crate) fn reduce<L: Limbs>(
  log_2_a_bound: u32,
  a: L,
  b: (Choice, L),
  negative_discriminant_abs: &L,
) -> (L, (Choice, L), L) {
  let (mut a, mut b, mut c) =
    reduce_to_lower_bound(log_2_a_bound, a, b, negative_discriminant_abs, 0);

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
