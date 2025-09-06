use crypto_bigint::{Choice, CtEq, CtLt, Zero, BitOr, BitOps, ShrVartime, Limb};

mod uint;
mod boxed_uint;

mod reduction;
pub(crate) use reduction::reduce;

/// A collection of limbs and associated helper methods, all expected to execute in constant-time.
///
/// The provided algorithms frequentally dance along Limb boundaries, performance requiring correct
/// decision of when to terminate execution of a given function. This API unifies `Uint` and
/// `BoxedUint` (in a way `Integer` appeared ineligible for) while providing the niche methods
/// required for performance.
///
/// TODO: Replace with `UintRef`.
trait Limbs:
  Sized
  + Clone
  + AsRef<[Limb]>
  + AsMut<[Limb]>
  + From<u8>
  + CtEq
  + Zero
  + BitOr<Output = Self>
  + BitOps
  + ShrVartime
{
  fn zero(limbs: usize) -> Self;

  fn shl(&self, bits: u32) -> Self;
  fn carrying_add(&self, b: &Self, carry: Limb) -> (Self, Limb);
  fn widening_square(&self) -> (Self, Self);
  // Divide `num`  by `denom`, returning the low bits.
  //
  // Returns `0` if passed `0` for the denominator.
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self;

  #[inline(always)]
  fn double(&self, limbs: usize) -> Self {
    let mut two_a = <Self as Limbs>::zero(limbs);
    for l in (1 .. limbs).rev() {
      <_ as AsMut<[Limb]>>::as_mut(&mut two_a)[l] = (<_ as AsRef<[Limb]>>::as_ref(&self)[l] << 1) |
        (<_ as AsRef<[Limb]>>::as_ref(&self)[l - 1] >> (Limb::BITS - 1));
    }
    <_ as AsMut<[Limb]>>::as_mut(&mut two_a)[0] = <_ as AsRef<[Limb]>>::as_ref(&self)[0] << 1;
    two_a
  }

  #[inline(always)]
  fn ct_select(&self, b: &Self, limbs: usize, choice: Choice) -> Self {
    let mut res = <Self as Limbs>::zero(limbs);
    for l in 0 .. limbs {
      <_ as AsMut<[Limb]>>::as_mut(&mut res)[l] = <_ as crypto_bigint::CtSelect>::ct_select(
        &<_ as AsRef<[Limb]>>::as_ref(&self)[l],
        &<_ as AsRef<[Limb]>>::as_ref(&b)[l],
        choice,
      );
    }
    res
  }

  #[inline(always)]
  fn ct_swap(&mut self, b: &mut Self, limbs: usize, choice: Choice) {
    for l in 0 .. limbs {
      <_ as crypto_bigint::CtSelect>::ct_swap(
        &mut <_ as AsMut<[Limb]>>::as_mut(self)[l],
        &mut <_ as AsMut<[Limb]>>::as_mut(b)[l],
        choice,
      );
    }
  }

  #[inline(always)]
  fn gt(&self, b: &Self, limbs: usize) -> Choice {
    let mut carry = Limb::ZERO;
    for l in 0 .. limbs {
      (_, carry) = <_ as AsRef<[Limb]>>::as_ref(&b)[l]
        .borrowing_sub(<_ as AsRef<[Limb]>>::as_ref(&self)[l], carry);
    }
    Choice::from((carry.0 & 1) as u8)
  }

  #[inline(always)]
  fn lt(&self, b: &Self, limbs: usize) -> Choice {
    crypto_bigint::UintRef::new(&self.as_ref()[.. limbs])
      .ct_lt(&crypto_bigint::UintRef::new(&b.as_ref()[.. limbs]))
  }
}
