use crypto_bigint::{Choice, BitOps, ShrVartime, Limb, UintRef};

/// A collection of limbs and associated helper methods.
///
/// The provided algorithms frequentally dance along `Limb` boundaries, performance requiring
/// correct decision of when to terminate execution of a given function. This API unifies `Uint`
/// and `BoxedUint` (in a way `Integer` appeared ineligible for) while providing the niche methods
/// required for performance.
///
/// Implementations MAY iterate up to the `limbs` argument (for performance) or MAY ignore it.
/// Callers MUST NOT expect that if they specify a `limbs` argument, operations will only occur to
/// that subset of limbs, and any results are undefined when any non-included limbs are non-zero.
/// Callers MUST NOT specify more `limbs` than the value has.
///
/// Implementations MUST implement all functions in time constant to the value of the inputs,
/// except for the amount of limbs, unless otherwise stated. Implementations MUST NOT panic for any
/// input which the caller MAY pass.
//
// TODO: Replace with `UintRef`.
pub(super) trait Limbs: AsRef<[Limb]> + AsMut<[Limb]> + BitOps + ShrVartime {
  /// Square the value, returning the `(lo, hi)` terms.
  ///
  /// Implementations MUST ensure each part of the result has an amount of limbs equal to how many
  /// limbs the input has.
  fn widening_square(&self) -> (Self, Self);

  /// Divide `num`  by `denom`, returning the low bits.
  ///
  /// Callers MUST ensure all parts of the numerator have an equivalent amount of limbs.
  ///
  /// Implementations MUST return `0` if passed `0` for the denominator.
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
  ac_lo.set_bit_vartime(ac_lo.bits_precision() - 2, four_ac_hi.bit_vartime(0));
  ac_lo.set_bit_vartime(ac_lo.bits_precision() - 1, four_ac_hi.bit_vartime(1));
  let ac_hi = four_ac_hi.unbounded_shr_vartime(2);
  let ac = (ac_lo, ac_hi);

  L::wrapping_div(ac, a)
}
