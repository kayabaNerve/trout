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
//!
//! Currently, no bounds on the value of `c` is established. This is a potential spot for
//! optimization.

use crypto_bigint::{Choice, CtSelect, CtAssign, Zero, Limb, UintRef};

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

/// Reduce by one bit if `b >= 2a` and `(floor(log_2(|b|)) + 1) == b_bits_bound`.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `a <= c` (such as forms output of `a_lte_c`)
/// - `ceil(log_2(max(|b|))) <= b_bits_bound` when `b_lte_2a == false`
///
/// Yield an equivalent form `(a', b', c')` such that:
/// - `a' = a`
/// - `floor(log_2(|b'|)) <= floor(log_2(|b|)) - 1` if `|b| > 2 a` and
///   `(floor(log_2(|b|)) + 1) == b_bits_bound`, else `(a', b', c') = (a, b, c)`
///
/// This is intended to perform _most_ steps of the reduction algorithm but explicitly not the last
/// steps. This allows it to optimize around certain edge cases. Specifically, it corresponds to
/// steps 3 and 6 of Algorithm 1, or a NOP if step 3's branch would not execute.
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
  b_lte_2a: &mut Choice,
  limbs: usize,
  b_bits_bound: u32,
) {
  #[cfg(debug_assertions)]
  {
    use crypto_bigint::CtGt;

    debug_assert!(bool::from(a.lt(c, <_ as AsRef<[Limb]>>::as_ref(c).len())));
    // Either `b <= 2a` or `b.1.bits() <= b_bits_bound`
    debug_assert!(bool::from((*b_lte_2a) | (!b.1.bits().ct_gt(&b_bits_bound))));
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(a).len());
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&b.1).len());
  }

  // Step 3

  /*
    Because this check is only valid when `(2 a, b)` fit within `limbs` limbs, short-circuit if we
    know `b <= 2a`, in which case `limbs` may not be well-defined.
  */
  let b_gt_2_a = (!*b_lte_2a) & {
    let mut two_a = a.clone();
    let two_a_ref = UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut two_a)[.. limbs]);
    two_a_ref.shl1_assign();
    // If `2a - b.1` has a borrow afterwards, then `b.1 > 2a`
    !two_a_ref.borrowing_sub_assign(b.1, Limb::ZERO).is_zero()
  };
  /*
    Update `b_lte_2a`.

    If `b_lte_2a` is set, this will never unset it, as `b_gt_2_a` won't be set if `b_lte_2a` was.
  */
  *b_lte_2a = !b_gt_2_a;

  /*
    Only run this iteration if this specific bit of `b` is in fact set.

    This is a correct optimization, as we run for all bits regardless. It also is an optimization
    as it avoids having to determine the amount of bits in `b`, instead assuming it equal to the
    bound (or performing a NOP).

    This does slightly overload `b_gt_2_a` as a pseudo-`should_iterate`.
  */
  let b_gt_2_a = b_gt_2_a & Choice::from(b.1.bit_vartime(b_bits_bound.saturating_sub(1)) as u8);

  /*
    This definition is important as when `b_gt_2_a = true`, we have
    `floor(log_2(2 * (1 << m) * a)) = floor(log_2(b))`. This is foundational for further proofs.
  */
  let m = {
    let a_bits = UintRef::new(&<_ as AsRef<[Limb]>>::as_ref(&a)[.. limbs]).bits();
    // This is correct per the check this bit, the highest possible, was actually set
    let b_bits = b_bits_bound;
    // This is only well-defined if `a_bits < b_bits`
    let m = b_bits.wrapping_sub(a_bits).wrapping_sub(1);
    // Set `m = 0` if `m` wouldn't be well-defined otherwise
    <_ as CtSelect>::ct_select(&0, &m, b_gt_2_a)
  };

  // Step 6

  // When `b_gt_2_a = true`, `((1 << m) * a) < b`, so this will fit in `limbs` limbs
  let mut m_a = a.clone();
  let m_a = UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut m_a)[.. limbs]);
  m_a.shl_assign(m);

  // epsilon b == |b| since epsilon = sgn(b)
  /*
    Instead of calculating `- epsilon m b + m m a`, we calculate `m (-|b| + m a)` to reduce the
    bit-length of the addition within the parentheses. As `m a < b` when `a < b`, the evaluation of
    the parentheses is negative and has an absolute value `< |b|` (which fits in `limbs` limbs).
  */
  let b_diff_m_a = {
    // This is a container of size `c` as we later operate on it with the bound the derivative is
    // `<= c`, which means this has to be large enough to contain a number `<= c`
    let mut b_diff_m_a = <L as Zero>::zero_like(&*c);
    {
      let b_diff_m_a =
        UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b_diff_m_a)[.. limbs]);
      b_diff_m_a.copy_from_slice(b.1.as_limbs());
      b_diff_m_a.borrowing_sub_assign(m_a, Limb::ZERO);
    }
    b_diff_m_a
  };

  /*
    The following does _not_ swap `c, a`, as we always perform any necessary swap during the next
    iteration's step 2 regardless. This means our `c` is updated to the paper's output `a`, and our
    `a` is left as-is.

    Note that in terms of this original paper which outputs `(a, b, c)`, this outputs `(c, b, a)`,
    which is not an equivalent form. The equivalent form would be `(c, -b, a)`. The paper is
    missing a negation on the output of its form, and once that's considered, this is equivalent.
  */

  /*
    We need to prove that `c >= (m b - m^2 a)`. We do so with the claim the output `c'` will be a
    positive integer, and therefore `c` MUST be greater than or equal to `m b - m^2 a` (when
    `b_gt_2_a = true`), as else `c'` would be negative.

    We know each intermediate form is equivalent to the input form, and therefore as for input
    `(a, b, c)` satisfying `b^2 - (4 a c) = delta`, we have `b'^2 - (4 a' c') = delta`. As
    `delta < 0`, and `b^2 >= 0`, `4 a' c'` MUST be a positive number. As our algorithm sets
    `a' = a` where `a` is positive, `c'` must be positive as well.
  */
  {
    /*
      Because `c` is greater than or equal to this value, this will fit within a container which
      fits `c`, where `b_diff_m_a` is a container of size equal to `c`'s container (making this
      `shl` call well-defined).
    */
    let mut m_b_diff_m_square_a = b_diff_m_a.clone();
    UintRef::new_mut(<_ as AsMut<[Limb]>>::as_mut(&mut m_b_diff_m_square_a))
      .unbounded_shl_assign(m);
    // This subtraction is well-defined as `c >= m_b_diff_m_square_a` when `b_gt_2_a = true`
    let mut borrow = Limb::ZERO;
    for l in 0 .. <_ as AsRef<[Limb]>>::as_ref(c).len() {
      // When `b_gt_2_a = false`, we subtract `0`, effecting a NOP
      let to_subtract = Limb::ct_select(
        &Limb::ZERO,
        &<_ as AsRef<[Limb]>>::as_ref(&m_b_diff_m_square_a)[l],
        b_gt_2_a,
      );

      let limb = &mut <_ as AsMut<[Limb]>>::as_mut(c)[l];
      let new_limb;
      (new_limb, borrow) = limb.borrowing_sub(to_subtract, borrow);
      *limb = new_limb;
    }
  }

  {
    let mut borrow = Limb::ZERO;
    // `|b|, 2 m a` have equivalent bit-length so their difference will be smaller, fitting into
    // any container `|b|` does
    for l in 0 .. limbs {
      let b_diff_2_m_a_limb;
      (b_diff_2_m_a_limb, borrow) =
        <_ as AsRef<[Limb]>>::as_ref(&b_diff_m_a)[l].borrowing_sub(m_a[l], borrow);
      // This writes the difference directly to `b`, but only when `b_gt_2_a = true`
      // (and we should iterate)
      b.1[l].ct_assign(&b_diff_2_m_a_limb, b_gt_2_a);
    }
    // If `b_gt_2_a = false`, set `borrow = 0`, so the next operations are guaranteed to be a NOP
    let borrow = Limb::ct_select(&Limb::ZERO, &borrow, b_gt_2_a);

    // If this underflowed (`2 m a < |b|`) and `borrow = 1`, apply the logical NOT to take the
    // absolute value
    let mut overflow_carry = Limb::ONE & borrow;
    // If `2 m a < |b|`, flip the sign of the result
    // `overflow_carry \in {0, 1}`, making this cast safe, and is `1` if `2 m a < |b|`
    #[expect(clippy::as_conversions, clippy::cast_possible_truncation)]
    {
      *b.0 ^= Choice::from(overflow_carry.0 as u8);
    }
    for l in 0 .. limbs {
      let limb = &mut b.1[l];
      *limb ^= borrow;
      let new_limb;
      (new_limb, overflow_carry) = limb.carrying_add(Limb::ZERO, overflow_carry);
      *limb = new_limb;
    }
  }
}

/// Reduce by one bit.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `a <= c` (such as forms output of `a_lte_c`)
/// - `ceil(log_2(max(a, |b|))) < 2^(limbs * Limb::BITS)`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(a).len())`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(&b.1).len())`
///
/// Yield an equivalent form `(a', b', c')` such that:
/// - `a' = a`
/// - `b' = 0` if `|b| == 2a`, else `(a', b', c') = (a, b, c)`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(b'.1).len())`
/// - `<L as AsRef::<[Limb]>>::as_ref(c').len()) = <L as AsRef::<[Limb]>>::as_ref(c).len())`
///
/// This is intended to correspond to steps 4 and 6 of Algorithm 1, or a NOP if `m != 1`.
// As this function is derivative of `reduce_to_next_bit`, it lacks internal comments which would
// be identical between the two.
#[inline(always)]
fn reduce_second_to_last_bit<L: Limbs>(a: &L, b: &mut (Choice, L), c: &mut L, limbs: usize) {
  #[cfg(debug_assertions)]
  {
    debug_assert!(bool::from(a.lt(c, <_ as AsRef<[Limb]>>::as_ref(c).len())));
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(a).len());
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&b.1).len());
  }

  let b_eq_2_a = b.1.eq(&a.clone().double(limbs), limbs);

  // `c - m |b| + m^2 a = c - |b| + a` when `m = 1`
  {
    let b_diff_a = {
      let mut b_diff_a = <L as Zero>::zero_like(&*c);
      {
        let b_diff_a = UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b_diff_a)[.. limbs]);
        b_diff_a.copy_from_slice(&<_ as AsRef<[Limb]>>::as_ref(&b.1)[.. limbs]);
        b_diff_a
          .borrowing_sub_assign_slice(&<_ as AsRef<[Limb]>>::as_ref(&a)[.. limbs], Limb::ZERO);
      }
      b_diff_a
    };

    let mut borrow = Limb::ZERO;
    for l in 0 .. <_ as AsRef<[Limb]>>::as_ref(c).len() {
      let to_subtract =
        Limb::ct_select(&Limb::ZERO, &<_ as AsRef<[Limb]>>::as_ref(&b_diff_a)[l], b_eq_2_a);

      let limb = &mut <_ as AsMut<[Limb]>>::as_mut(c)[l];
      let new_limb;
      (new_limb, borrow) = limb.borrowing_sub(to_subtract, borrow);
      *limb = new_limb;
    }
  }

  // `b - epsilon 2 m a = 0` when `|b| = 2 a` as then `m = 1`
  for l in 0 .. limbs {
    <_ as AsMut<[Limb]>>::as_mut(&mut b.1)[l].ct_assign(&Limb::ZERO, b_eq_2_a);
  }
}

/// Reduce by one bit.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `a <= c` (such as forms output of `a_lte_c`)
/// - `ceil(log_2(max(a, |b|))) < 2^(limbs * Limb::BITS)`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(a).len())`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(&b.1).len())`
///
/// Yield an equivalent form `(a', b', c')` such that:
/// - `a' = a`
/// - `|b'| <= a` if `a <= |b| < 2 a`, else `(a', b', c') = (a, b, c)`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(b'.1).len())`
/// - `<L as AsRef::<[Limb]>>::as_ref(c').len()) = <L as AsRef::<[Limb]>>::as_ref(c).len())`
///
/// This is intended to correspond to steps 4 and 6 of Algorithm 1, or a NOP if `m != 1`.
// As this function is a derivative of `reduce_to_next_bit`, it lacks internal comments which would
// be identical between the two.
#[inline(always)]
fn reduce_last_bit<L: Limbs>(a: &L, b: &mut (Choice, L), c: &mut L, limbs: usize) {
  #[cfg(debug_assertions)]
  {
    debug_assert!(bool::from(a.lt(c, <_ as AsRef<[Limb]>>::as_ref(c).len())));
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(a).len());
    debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&b.1).len());
  }

  let m_eq_1 = {
    let b_gte_a = !b.1.lt(a, limbs);
    let b_lt_2a = b.1.lt(&a.clone().double(limbs), limbs);
    b_gte_a & b_lt_2a
  };

  let b_diff_a = {
    let mut b_diff_a = <L as Zero>::zero_like(&*c);
    let mut borrow = Limb::ZERO;
    for l in 0 .. limbs {
      (<_ as AsMut<[Limb]>>::as_mut(&mut b_diff_a)[l], borrow) = <_ as AsRef<[Limb]>>::as_ref(&b.1)
        [l]
        .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&a)[l], borrow);
    }
    b_diff_a
  };

  {
    let mut borrow = Limb::ZERO;
    for l in 0 .. <_ as AsRef<[Limb]>>::as_ref(c).len() {
      let to_subtract =
        Limb::ct_select(&Limb::ZERO, &<_ as AsRef<[Limb]>>::as_ref(&b_diff_a)[l], m_eq_1);

      let limb = &mut <_ as AsMut<[Limb]>>::as_mut(c)[l];
      let new_limb;
      (new_limb, borrow) = limb.borrowing_sub(to_subtract, borrow);
      *limb = new_limb;
    }
  }

  // Because we know `|b| < 2 a` if `m_eq_1`, we calculate the difference of `|b|, 2 a` as
  // `a - (|b| - a) = a - |b| + a`
  {
    let mut borrow = Limb::ZERO;
    for l in 0 .. limbs {
      let b_diff_2_a_limb;
      (b_diff_2_a_limb, borrow) = <_ as AsRef<[Limb]>>::as_ref(a)[l]
        .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&b_diff_a)[l], borrow);
      <_ as AsMut<[Limb]>>::as_mut(&mut b.1)[l].ct_assign(&b_diff_2_a_limb, m_eq_1);
    }
    b.0 ^= m_eq_1;
  }
}

/// Reduce by two bits.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `a <= c` (such as forms output of `a_lte_c`)
/// - `ceil(log_2(max(a, |b|))) < 2^(limbs * Limb::BITS)`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(a).len())`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(&b.1).len())`
///
/// Yield an equivalent form `(a', b', c')` such that:
/// - `a' = a`
/// - `|b'| <= a` if `|b| <= 2 a`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(b'.1).len())`
/// - `<L as AsRef::<[Limb]>>::as_ref(c').len()) = <L as AsRef::<[Limb]>>::as_ref(c).len())`
///
/// This is intended to correspond to steps 4 and 6 of Algorithm 1, or a NOP if `|b| < a`.
#[inline(always)]
fn reduce_last_two_bits<L: Limbs>(a: &mut L, b: &mut (Choice, L), c: &mut L, limbs: usize) {
  // This outputs `|b'| <= a` if `|b| == 2 a`
  reduce_second_to_last_bit(&*a, b, c, limbs);
  a_lte_c(a, &mut b.0, c);
  // This outputs `|b'| <= a` if `|b| < 2 a`
  reduce_last_bit(&*a, b, c, limbs);
}

/// Normalize an almost-reduced element.
///
/// For a positive definite binary quadratic form `(a, b, c)` such that:
/// - `b^2 - 4ac = delta` where `delta < 0` (the form is well-defined for a negative discriminant)
/// - `0 <= a, c` (`a` and `c` aren't negative, as enforced by the type system)
/// - `|b| <= a`
/// - `a, c < 2^(limbs * Limb::BITS)`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(&a).len())`
/// - `limbs <= <L as AsRef::<[Limb]>>::as_ref(&c).len())`
///
/// Yield the reduced equivalent form `(a', b', c')` such that:
/// - `|b'| <= a' <= c'`
/// - `b' >= 0` if `(|b'| == a') || (|b'| == c')`
///
/// This is intended to correspond to steps 2 and 5 of Algorithm 1.
#[inline(always)]
fn normalize<L: Limbs>(mut a: L, mut b: (Choice, L), mut c: L) -> (L, (Choice, L), L) {
  a_lte_c(&mut a, &mut b.0, &mut c);
  // Set `b` to be positive if `|b| == a'` (as `a' <= c`)
  b.0 |= b.1.ct_eq(&a);
  // Set `b` to be positive if `b == 0` (in order to not return -0)
  b.0 |= b.1.is_zero();
  (a, b, c)
}

/// Calculate `c` such that `b^2 - 4ac = delta`.
///
/// The following bounds are present:
/// - `delta < 0`
/// - `ceil(log_2(a)) <= log_2_a_bound`
/// - `|b| < 2 a`
/// - There is an integer solution for `c` in `b^2 - 4 a c = delta`.
/// - `(a - delta) < 2^(<L as AsRef::<[Limb]>>::as_ref(&b.1).len() * Limb::BITS)``
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

/// Partially reduce an element.
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
/// - `(a', b', c')` is reduced or `a' < b'`
///
/// As composition is presumably programmed to compose `b`-bit-length numbers, where composition
/// outputs `2 * b`-bit-length numbers, this function intends to solely perform the necessary
/// reduction such that the numbers are once again of `b`-bit-length (and able to be composed
/// again). While these forms are not reduced, they may still usable for composition _without_
/// performing a full reduction (which would take roughly twice as long). This allows deferring a
/// full reduction until one _needs_ a reduced form.
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
    Each iteration will reduce the bit length of `b` by at least `1`, until `b <= 2 a` if each
    iteration applies.
  */
  {
    let mut limbs = original_limbs;
    let mut progress_in_limb = Limb::BITS - (log_2_b_bound % Limb::BITS);
    let (b_sign, mut b_value) =
      (&mut b.0, UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut b.1)[.. limbs]));
    let mut b_lte_2a = Choice::FALSE;
    for bits in ((discriminant_bits / 2) ..= log_2_b_bound).rev() {
      a_lte_c(&mut a, b_sign, &mut c);

      // Confirm each iteration achieved the expected bound
      #[cfg(debug_assertions)]
      {
        debug_assert!(bool::from({
          use crypto_bigint::CtLt;
          // `b.1.bits() <= (bits + 1)`
          b_lte_2a | b_value.bits().ct_lt(&(bits + 1))
        }));
      }

      reduce_to_next_bit(&a, (b_sign, b_value), &mut c, &mut b_lte_2a, limbs, bits);

      if progress_in_limb == Limb::BITS {
        progress_in_limb = 0;
        limbs -= 1;
        b_value = b_value.leading_mut(limbs);
      }
      progress_in_limb += 1;
    }
  }

  /*
    The above loop either output:
    - A `b` which is reduced (barring any potentially required normalization)
    - An unreduced `b'` such that `b'^2 < |delta|`
    - An unreduced `b'` such that `b'^2 >= |delta|`

    This as if the loop above ran, it either reduced to the desired bit-length _or_ some iterations
    were NOPs. A NOP would only occur if `b' <= 2a`, in which case the `b'` value is almost reduced
    (barring any potentially required normalization). We apply the final reduction steps now, which
    are NOPs if `b > 2a`, but in which case, all iterations of the above loop ran and we know for
    sure `b'^2 < |delta|`.

    Note a reduced `b'` is guaranteed to satisfy `b'^2 < |delta|`. This is as, for a negative
    discriminant (as we bound),

    - `b'^2 <= a' c'`

    This is as `b' <= a' <= c'`.

    - `-4 a' c' + b'^2 = delta`

    This is a simply rewrite of `b'^2 - 4 a' c' = delta`.

    - `0 <= (log_2(4 a' c') - log_2(|delta|)) < 1`

    This is as `4 a' c', delta` have an absolute difference of `b^2` where `b^2 <= a' c'`.

    - `1 <= (log_2(|delta|) - log_2(a' c')) < 2`

    This is a simple rewrite of the prior bound.

    Letting us finally bound `log_2(|delta|) > log_2(b'^2)`.
  */
  a_lte_c(&mut a, &mut b.0, &mut c);
  /*
    This operates over the full-width integers as while `b <= 2 a`, and this is proven to terminate
    after the application of `reduce_last_two_bits`, it's not actually proven that our `b` is
    within two bits of `b'`. The final reduction steps may reduce multiple bits at once.
  */
  reduce_last_two_bits(&mut a, &mut b, &mut c, original_limbs);

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
/// - `b' >= 0` if `(|b'| == a') || (|b'| == c')`
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
    let mut b_lte_2a = Choice::FALSE;
    for bits in (0 ..= log_2_b_bound).rev() {
      a_lte_c(&mut a, b_sign, &mut c);

      #[cfg(debug_assertions)]
      {
        debug_assert!(bool::from({
          use crypto_bigint::CtLt;
          b_lte_2a | b_value.bits().ct_lt(&(bits + 1))
        }));
      }

      reduce_to_next_bit(&a, (b_sign, b_value), &mut c, &mut b_lte_2a, limbs, bits);

      if progress_in_limb == Limb::BITS {
        progress_in_limb = 0;
        limbs -= 1;
        b_value = b_value.leading_mut(limbs);
      }
      progress_in_limb += 1;
    }
  }

  a_lte_c(&mut a, &mut b.0, &mut c);
  reduce_last_two_bits(&mut a, &mut b, &mut c, original_limbs);
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
