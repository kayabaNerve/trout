use crypto_bigint::{Choice, CtEq, CtLt, CtSelect, Zero, BitOps, ShrVartime, Limb, UintRef};

mod uint;
mod boxed_uint;

mod reduction;
pub(crate) use reduction::{partial_reduce, reduce};

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
trait Limbs: Sized + AsRef<[Limb]> + AsMut<[Limb]> + CtEq + Zero + BitOps + ShrVartime {
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

  /// The number but with precision equal to `self`.
  ///
  /// This is equivalent to [`crypto_bigint::Zero::zero_like`] but avoids requiring `Self: Clone`.
  /// We do not want to bound `Self: Clone` for performance reasons. Specifically, it's a goal of
  /// the reduction algorithm to not allocate at all (for performance reasons), this one function
  /// being necessary in one spot and the current sole exception.
  fn like_zero(&self) -> Self;

  /// Swap the values of `self` and `b` if `choice` is `true`.
  #[inline(always)]
  fn swap(&mut self, b: &mut Self, choice: Choice) {
    let a = &mut <_ as AsMut<[Limb]>>::as_mut(self);
    let b = &mut <_ as AsMut<[Limb]>>::as_mut(b);
    for (a, b) in a.iter_mut().zip(b.iter_mut()) {
      <_>::ct_swap(a, b, choice);
    }
  }

  /// `true` if `self < b` and `false` otherwise.
  #[inline(always)]
  fn lt(&self, b: &Self, limbs: usize) -> Choice {
    UintRef::new(&self.as_ref()[.. limbs]).ct_lt(UintRef::new(&b.as_ref()[.. limbs]))
  }

  /// `true` if `self == b` and `false` otherwise.
  #[cfg(debug_assertions)]
  #[inline(always)]
  fn eq(&self, b: &Self, limbs: usize) -> Choice {
    UintRef::new(&self.as_ref()[.. limbs]).ct_eq(UintRef::new(&b.as_ref()[.. limbs]))
  }
}

/// Check if the first argument is less than the second argument.
///
/// This functions runs in time constant to the value in the limbs, but in time variable to the
/// amount of limbs. This function correctly handles when the amount of limbs in `first` differs
/// from `second`.
///
/// This implementation is functionally equivalent to `first < second.shl1()`, but avoids
/// allocating a collection of limbs to store `second.shl1()`.
#[cfg(debug_assertions)]
fn first_lt_2_second<'a>(mut first: &'a [Limb], mut second: &'a [Limb]) -> Choice {
  // Ensure `second` has the same amount of, or more, limbs
  if first.len() < second.len() {
    core::mem::swap(&mut first, &mut second);
  }

  // The carry from calculating `2 second` limb-by-limb
  let mut two_second_carry = Limb::ZERO;
  // We calculate the borrow from `first - 2 second`, which is non-zero if `first < 2 second`
  let mut borrow = Limb::ZERO;

  // Handle all mutual limbs in `first, second`
  for (first_limb, second_limb) in first.iter().zip(second) {
    let two_second_limb = ((*second_limb) << 1) | two_second_carry;
    two_second_carry = (*second_limb) >> (Limb::BITS - 1);
    let _first_diff_2_second_limb;
    (_first_diff_2_second_limb, borrow) = first_limb.borrowing_sub(two_second_limb, borrow);
  }

  /*
    If we've exhausted `second`'s limbs, apply the final carry from `2 second` (as `2 second` may
    exceed the precision of `second` itself).

    Note this only considers the non-mutually-present limbs in `first`, not any
    non-mutually-present limbs in `second`, as we ensured `second` had less (or an equal amount of)
    limbs.
  */
  if let Some(remaining_first_limb) = first.get(second.len()) {
    let _first_diff_2_second_limb;
    (_first_diff_2_second_limb, borrow) =
      remaining_first_limb.borrowing_sub(two_second_carry, borrow);

    // If any remaining limbs in `first` are non-zero, clear the borrow, which is correct as we can
    // bound the borrow to be either `0` or `1`
    for first_limb in first.iter().skip(second.len() + 1) {
      use crypto_bigint::CtAssign;
      borrow.ct_assign(&Limb::ZERO, !first_limb.is_zero());
    }
  } else {
    // If there are no more limbs in `first`, then the carry from `2 second` becomes part of the
    // borrow
    borrow = borrow.wrapping_add(two_second_carry);
  }
  !borrow.is_zero()
}
