use crypto_bigint::{Choice, CtEq, CtLt, Zero, BitOps, ShrVartime, Limb, UintRef};

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
trait Limbs: Sized + Clone + AsRef<[Limb]> + AsMut<[Limb]> + CtEq + Zero + BitOps + ShrVartime {
  /// Perform an addition, with carry.
  ///
  /// Callers MUST ensure the two values have an equivalent amount of limbs.
  ///
  /// Returns the sum value and the updated carry value.
  fn carrying_add(&self, b: &Self, carry: Limb) -> (Self, Limb) {
    let mut result = self.clone();
    let carry = UintRef::new_mut(result.as_mut()).carrying_add_assign_slice(b.as_ref(), carry);
    (result, carry)
  }

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

  /// Double the current value.
  ///
  /// The result is undefined on overflow.
  #[cfg(debug_assertions)]
  #[inline(always)]
  fn double(mut self, limbs: usize) -> Self {
    UintRef::new_mut(&mut <_ as AsMut<[Limb]>>::as_mut(&mut self)[.. limbs]).shl1_assign();
    self
  }

  /// Swap the values of `self` and `b` if `choice` is `true`.
  #[inline(always)]
  fn swap(&mut self, b: &mut Self, limbs: usize, choice: Choice) {
    let a = &mut <_ as AsMut<[Limb]>>::as_mut(self);
    let b = &mut <_ as AsMut<[Limb]>>::as_mut(b);
    for (a, b) in a.iter_mut().zip(b.iter_mut()).take(limbs) {
      <_ as crypto_bigint::CtSelect>::ct_swap(a, b, choice);
    }
  }

  /// `true` if `self < b` and `false` otherwise.
  #[inline(always)]
  fn lt(&self, b: &Self, limbs: usize) -> Choice {
    crypto_bigint::UintRef::new(&self.as_ref()[.. limbs])
      .ct_lt(crypto_bigint::UintRef::new(&b.as_ref()[.. limbs]))
  }

  /// `true` if `self == b` and `false` otherwise.
  #[cfg(debug_assertions)]
  #[inline(always)]
  fn eq(&self, b: &Self, limbs: usize) -> Choice {
    crypto_bigint::UintRef::new(&self.as_ref()[.. limbs])
      .ct_eq(crypto_bigint::UintRef::new(&b.as_ref()[.. limbs]))
  }
}
