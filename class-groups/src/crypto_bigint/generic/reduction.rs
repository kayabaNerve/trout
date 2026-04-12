// Reduction algorithm from https://eprint.iacr.org/2022-466, implemented over types descending
// from crypto-bigint with a thin abstraction layer.

use crypto_bigint::{Choice, CtEq, CtSelect, Limb};

use super::Limbs;

#[inline(always)]
fn step_two<L: Limbs>(a: L, b: (Choice, L), c: L, limbs: usize) -> (L, (Choice, L), L) {
  let c_lt_a = c.lt(&a, limbs);
  let mut a_apo = a;
  let mut c_apo = c;
  <L as Limbs>::ct_swap(&mut a_apo, &mut c_apo, limbs, c_lt_a);

  /*
    This line differs from the paper, whose described algorithm has a pair of typos (as
    further evidenced by the correctness proof transcribing line 6,
    "[C - epsilon m B + m**2 A]" as "[C, - epsilon m B + A**2]").

    This a modification necessary for the form reduced to be equivalent
    `(a, b, c) -> (c, -b, a)`.
  */
  let b_apo = ((b.0 ^ c_lt_a), b.1);
  (a_apo, b_apo, c_apo)
}

#[inline(always)]
fn reduce_to_next_bit<L: Limbs>(
  a: L,
  b: (Choice, L),
  c: L,
  a_max_b_bits_bound: u32,
) -> (L, (Choice, L), L) {
  let limbs = usize::try_from((a_max_b_bits_bound + 4).div_ceil(Limb::BITS)).unwrap();
  debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&a).len());
  debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&b.1).len());

  // Step 2
  let (a, mut b, mut c) = step_two(a.clone(), b, c, limbs);

  // Step 3
  let two_a = a.double(limbs);
  let b_gt_2_a = b.1.gt(&two_a, limbs);

  let m = {
    let b_bits = b.1.bits().wrapping_sub(1);
    let a_bits = a.bits().wrapping_sub(1);
    // We set `m` as the amount of bits to shift by
    <_ as CtSelect>::ct_select(
      &(b_bits.wrapping_sub(a_bits).wrapping_sub(1)),
      &0,
      a.is_zero() | (!b_gt_2_a),
    )
  };

  /*
    We don't implement steps 4, 5, as we only perform the binary reduction before moving to
    the Euclidean algorithm for the final steps. If we did the conditional `m` here, we
    wouldn't be able to optimize via its structure (due to needing to calculate both paths in
    order to not reveal which was taken).
  */

  // Step 6

  /*
    `b**2 - 4ac = discriminant`

    `b` starts as the bit-length of the discriminant, so `b**2` is twice the bit-length and
    `a, c` is on average twice the bit-length yet each up to twice the bit-length of the
    discriminant. Note `4ac` is within `1` of the bit-length of `b**2` when
    `b**2 > |discriminant|`.

    Because `b` decreases in size with each iteration (cite 2022-466), `4ac` must also
    decreases in size (to remain within `1` of the bit-length of `b**2`). This is until
    `b**2 <= |discriminant|`, at which point `4ac` is less than the bit-length of the
    discriminant plus `1`.

    Since we enforce `a < c` at the start of each iteration of the loop, we know the
    bit-length of `a` must be less than or equal to the bit-length of `c`.

    `m` is unfortunately bounded to `log_2(b) - log_2(a)`, so that is the bit-length of the
    discriminant minus potentially 0. We then need to perform the shifts `a << m` and
    `a << m**2`. For the former, this means operating with the existing integer size. For the
    latter, it is again the existing integer size as if `m` is high, `a` itself is low.
  */

  // This has bit-length approximate to `b`, so it fits within `L`
  let m_a = a.shl(m);
  // epsilon b == |b| since epsilon = sgn(b)
  // let epsilon_b = b.1;
  /*
    We calculate `m (- epsilon b + m a)` to reduce the bit-length of the addition performed.

    As `m a < epsilon b`, we calculate `epsilon b - m a`, leaving us with the negative of the
    desired terms.
  */
  let mut m_a_minus_epsilon_b_neg = <L as Limbs>::zero(limbs);
  let mut carry = Limb::ZERO;
  for l in 0 .. limbs {
    (<_ as AsMut<[Limb]>>::as_mut(&mut m_a_minus_epsilon_b_neg)[l], carry) =
      <_ as AsRef<[Limb]>>::as_ref(&b.1)[l]
        .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&m_a)[l], carry);
  }
  debug_assert!(bool::from(carry.ct_eq(&Limb::ZERO) | (!b_gt_2_a)));

  // Scale by `m`
  /*
    We now need to calculate `a_{i+1} = c_i - epsilon m b_i + m**2 a_i`.

    Because `b` decreases, `a` decreases, as extensively described above. That means, because
    it was prior in bounds, this decreased version will be. By the point `a` starts
    increasing in size again, it's capped within bounds.

    This also means that we have either `x + |m y|`, or `x - |m y|` where `x, y` and the
    result fits within the current integer size. For the first case, where `m y` is positive and
    added, `m y` must have bit-length less than or equal to the result. For the second case, where
    `m y` is negative and subtracted, it is at most of bit-length `x` since the result is
    guaranteed to be positive.

    Accordingly, `m y` fits within either the bounds of the result or the bounds of `x`.
    Since both fit within the current integer size, `m y` does and we don't need to promote it to
    a wider type.
  */
  let m_square_a_minus_epsilon_m_b_abs = m_a_minus_epsilon_b_neg.shl(m);

  let mut a_res = <L as Limbs>::zero(limbs);
  let mut carry = Limb::ZERO;
  for l in 0 .. limbs {
    (<_ as AsMut<[Limb]>>::as_mut(&mut a_res)[l], carry) = <_ as AsRef<[Limb]>>::as_ref(&c)[l]
      .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&m_square_a_minus_epsilon_m_b_abs)[l], carry);
  }
  debug_assert!(bool::from(carry.ct_eq(&Limb::ZERO) | (!b_gt_2_a)));

  // This will have a bit-length approximate to B, which fits within a L, so this is fine
  let b_res = {
    let two_m_a = m_a.double(limbs);
    let difference = {
      let mut difference = <L as Limbs>::zero(limbs);
      <_ as AsMut<[Limb]>>::as_mut(&mut difference)[.. limbs]
        .copy_from_slice(&<_ as AsRef<[Limb]>>::as_ref(&b.1)[.. limbs]);
      let carry = crypto_bigint::UintRef::new_mut(&mut difference.as_mut()[.. limbs])
        .borrowing_sub_assign(crypto_bigint::UintRef::new(&two_m_a.as_ref()[.. limbs]), Limb::ZERO);
      // If this overflowed, apply the logical NOT to take the absolute value
      let mut overflow_carry = Limb::ONE & carry;
      for l in 0 .. limbs {
        <_ as AsMut<[Limb]>>::as_mut(&mut difference)[l] ^= carry;
        (<_ as AsMut<[Limb]>>::as_mut(&mut difference)[l], overflow_carry) =
          <_ as AsRef<[Limb]>>::as_ref(&difference)[l].carrying_add(Limb::ZERO, overflow_carry);
      }
      let b_lt_two_m_a = Choice::from((carry.0 & 1) as u8);
      (b_lt_two_m_a, difference)
    };
    // If epsilon = 1, these were positive and the difference is as-is
    // If epsilon = -1, these were negative and the difference must be negated
    // If epsilon = 0, !(b > 2 * a) so this doesn't matter
    (difference.0 ^ b.0, difference.1)
  };

  let c_res = &a;

  // Only write these values if this was the `m = 2**k` case
  let should_iterate = b_gt_2_a;
  let a_res = <L as Limbs>::ct_select(&a, &a_res, limbs, should_iterate);
  // The paper doesn't say to negate this here, but it was necessary when comparing the
  // results to the textbook algorithm's
  b.0 = <_ as CtSelect>::ct_select(&b.0, &!b_res.0, should_iterate);
  b.1 = <L as Limbs>::ct_select(&b.1, &b_res.1, limbs, should_iterate);
  c = <L as Limbs>::ct_select(&c, c_res, limbs, should_iterate);

  (a_res, b, c)
}

#[inline(always)]
fn reduce_second_to_last_bit<L: Limbs>(
  a: L,
  b: (Choice, L),
  c: L,
  a_max_b_bits_bound: u32,
) -> (L, (Choice, L), L) {
  let limbs = usize::try_from((a_max_b_bits_bound + 4).div_ceil(Limb::BITS)).unwrap();
  debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&a).len());
  debug_assert!(limbs <= <_ as AsRef::<[Limb]>>::as_ref(&b.1).len());

  let (a, mut b, mut c) = step_two(a.clone(), b, c, limbs);

  let b_gt_a = b.1.gt(&a, limbs);

  let m_a = &a;
  let mut m_a_minus_epsilon_b_neg = <L as Limbs>::zero(limbs);
  let mut carry = Limb::ZERO;
  for l in 0 .. limbs {
    (<_ as AsMut<[Limb]>>::as_mut(&mut m_a_minus_epsilon_b_neg)[l], carry) =
      <_ as AsRef<[Limb]>>::as_ref(&b.1)[l]
        .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&m_a)[l], carry);
  }
  debug_assert!(bool::from(carry.ct_eq(&Limb::ZERO) | (!b_gt_a)));

  let m_square_a_minus_epsilon_m_b_abs = m_a_minus_epsilon_b_neg;

  let mut a_res = <L as Limbs>::zero(limbs);
  let mut carry = Limb::ZERO;
  for l in 0 .. limbs {
    (<_ as AsMut<[Limb]>>::as_mut(&mut a_res)[l], carry) = <_ as AsRef<[Limb]>>::as_ref(&c)[l]
      .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&m_square_a_minus_epsilon_m_b_abs)[l], carry);
  }
  debug_assert!(bool::from(carry.ct_eq(&Limb::ZERO) | (!b_gt_a)));

  let b_res = {
    let two_m_a = m_a.double(limbs);
    let difference = {
      let mut difference = <L as Limbs>::zero(limbs);
      let mut carry = Limb::ZERO;
      for l in 0 .. limbs {
        (<_ as AsMut<[Limb]>>::as_mut(&mut difference)[l], carry) =
          <_ as AsRef<[Limb]>>::as_ref(&b.1)[l]
            .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&two_m_a)[l], carry);
      }
      let mut overflow_carry = Limb::ONE & carry;
      for l in 0 .. limbs {
        <_ as AsMut<[Limb]>>::as_mut(&mut difference)[l] ^= carry;
        (<_ as AsMut<[Limb]>>::as_mut(&mut difference)[l], overflow_carry) =
          <_ as AsRef<[Limb]>>::as_ref(&difference)[l].carrying_add(Limb::ZERO, overflow_carry);
      }
      let b_lt_two_m_a = Choice::from((carry.0 & 1) as u8);
      (b_lt_two_m_a, difference)
    };
    (difference.0 ^ b.0, difference.1)
  };

  let c_res = &a;

  // Only write these values if this was the `m = 1` case
  let should_iterate = b_gt_a;
  let a_res = <L as Limbs>::ct_select(&a, &a_res, limbs, should_iterate);
  b.0 = <_ as CtSelect>::ct_select(&b.0, &!b_res.0, should_iterate);
  b.1 = <L as Limbs>::ct_select(&b.1, &b_res.1, limbs, should_iterate);
  c = <L as Limbs>::ct_select(&c, c_res, limbs, should_iterate);

  (a_res, b, c)
}

#[inline(always)]
fn reduce_last_bit<L: Limbs>(a: L, b: (Choice, L), c: L) -> (L, (Choice, L), L) {
  let limbs = <_ as AsRef<[Limb]>>::as_ref(&a).len();
  let (a, mut b, c) = step_two(a, b, c, limbs);
  // Set `b` to be positive if `b == a`
  b.0 = !((!b.0) | b.1.ct_eq(&a));
  (a, b, c)
}

/// Reduce only ~half the bits in the values.
///
/// This is not a full reduction, but is sufficient to go from a wide representation to a normal
/// representation, as usable to perform further arithmetic without under/overflow.
#[allow(private_bounds)]
#[inline(always)]
pub(crate) fn partial_reduce<L: Limbs>(
  log_2_a_bound: u32,
  mut a: L,
  mut b: (Choice, L),
  negative_discriminant: &L,
) -> (L, (Choice, L), L) {
  debug_assert_eq!(
    <_ as AsRef::<[Limb]>>::as_ref(&a).len(),
    <_ as AsRef::<[Limb]>>::as_ref(&b.1).len()
  );

  let mut c = {
    // The `b` from composition is `% 2a`, so at most `b**2 = (2a-1)**2`. We increase this bound
    // to `b**2 = 4 a**2`. `(4 a**2) / 4a` would equal `a`, meaning `c <= a` even for `a, b`
    // directly from the composition formulas (and unreduced).

    // b**2 - 4ac = discriminant
    // b**2 = discriminant + 4ac
    // b**2 - discriminant = 4ac
    let (b_lo, b_hi) = b.1.widening_square();

    let (four_ac_lo, carry) = b_lo.carrying_add(negative_discriminant, Limb::ZERO);
    let (four_ac_hi, carry) =
      b_hi.carrying_add(&<L as Limbs>::zero(<_ as AsRef<[Limb]>>::as_ref(&a).len()), carry);
    debug_assert_eq!(carry, Limb::ZERO);

    let mut four_ac_lo = four_ac_lo.unbounded_shr_vartime(2);
    four_ac_lo.set_bit_vartime(four_ac_lo.bits_precision() - 2, four_ac_hi.bit_vartime(0));
    four_ac_lo.set_bit_vartime(four_ac_lo.bits_precision() - 1, four_ac_hi.bit_vartime(1));
    let four_ac_hi = four_ac_hi.unbounded_shr_vartime(2);
    let ac = (four_ac_lo, four_ac_hi);

    L::wrapping_div(ac, &a)
  };

  // Iterate from the current log2 of `a` to the log2 of the sqrt of the discriminant
  let sqrt_discriminant_bits = negative_discriminant.bits_vartime().div_ceil(2);
  for a_bits in ((log_2_a_bound / 2) ..= log_2_a_bound).rev() {
    (a, b, c) = reduce_to_next_bit(a, b, c, a_bits.max(sqrt_discriminant_bits) + 1);
  }
  // This is done here just for some normalization steps, not because there are the final bits,
  // though the operations are correct regardless
  let (a, b, c) = reduce_second_to_last_bit(a, b, c, sqrt_discriminant_bits);
  reduce_last_bit(a, b, c)
}

#[allow(private_bounds)]
#[inline(always)]
pub(crate) fn reduce<L: Limbs>(
  log_2_a_bound: u32,
  a: L,
  b: (Choice, L),
  negative_discriminant: &L,
) -> (L, (Choice, L), L) {
  let (mut a, mut b, mut c) = partial_reduce(log_2_a_bound, a, b, negative_discriminant);
  let sqrt_discriminant_bits = negative_discriminant.bits_vartime().div_ceil(2);
  for a_bits in (0 .. (log_2_a_bound / 2)).rev() {
    (a, b, c) = reduce_to_next_bit(a, b, c, a_bits.max(sqrt_discriminant_bits) + 1);
  }
  let (a, b, c) = reduce_second_to_last_bit(a, b, c, sqrt_discriminant_bits);
  reduce_last_bit(a, b, c)
}
