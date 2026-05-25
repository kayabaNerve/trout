use crypto_bigint::{Choice, ShrVartime, Limb, UintRef};

/// The required view over a collection of limbs to calculate the `c` coefficient.
///
/// Implementations MUST implement all functions in time constant to the value of the inputs,
/// except for the amount of limbs, unless otherwise stated. Implementations MUST NOT panic for any
/// input which the caller MAY pass.
pub(super) trait Limbs: AsRef<[Limb]> + AsMut<[Limb]> + ShrVartime {
  /// Square the value, returning the `(lo, hi)` terms.
  ///
  /// Implementations MUST ensure each part of the result has an amount of limbs equal to how many
  /// limbs the input has.
  fn widening_square(&self) -> (Self, Self);

  /// Divide `num`  by `denom`, returning the low bits.
  ///
  /// Callers MUST ensure all parts of the numerator have an equivalent amount of limbs. Callers
  /// MUST NOT request a division by `0`.
  ///
  /// Implementations MUST ensure the result has an amount of limbs equal to how many limbs each
  /// part of the input has.
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self;
}

/// Calculate `c` such that `b^2 - 4ac = delta`.
///
/// The following bounds are present:
/// - `delta < 0`
/// - `floor(log_2(a)) + 1 <= log_2_a_bound`
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
  // Shift the lowest two bits from `four_ac_hi` into the highest two bits of `ac_lo`
  *<_ as AsMut<[Limb]>>::as_mut(&mut ac_lo).last_mut().unwrap() |=
    <_ as AsRef<[Limb]>>::as_ref(&four_ac_hi)[0] << (Limb::BITS - 2);
  let ac_hi = four_ac_hi.unbounded_shr_vartime(2);
  let ac = (ac_lo, ac_hi);

  /*
    As `b^2` is positive yet `delta < 0`, `4ac` must be non-zero. Therefore, `a` must be non-zero
    if this is a valid form, making this division safe.
  */
  L::wrapping_div(ac, a)
}
