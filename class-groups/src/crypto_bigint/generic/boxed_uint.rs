use crypto_bigint::{CtSelect, Zero, Resize, ConcatenatingSquare, Limb, BoxedUint};

use super::Limbs;

impl Limbs for BoxedUint {
  fn zero(limbs: usize) -> Self {
    <Self as Zero>::zero().resize_unchecked(u32::try_from(limbs).unwrap() * Limb::BITS + 1)
  }

  fn shl(&self, bits: u32) -> Self {
    self.unbounded_shl(bits)
  }
  fn carrying_add(&self, b: &Self, carry: Limb) -> (Self, Limb) {
    self.carrying_add(b, carry)
  }
  fn widening_square(&self) -> (Self, Self) {
    let size = self.bits_precision();
    let square = self.concatenating_square().clone();
    let hi = (&square >> size).resize_unchecked(size);
    let lo = square.resize_unchecked(size);
    (lo, hi)
  }
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self {
    let denom_bits = u32::try_from(denom.as_limbs().len()).unwrap() * Limb::BITS;
    let num =
      num.1.resize_unchecked(2 * denom_bits).overflowing_shl_vartime(denom_bits).unwrap() | num.0;
    let denom_is_zero = denom.is_zero();
    let denom = <_ as CtSelect>::ct_select(
      denom,
      &BoxedUint::one().resize_unchecked(denom.bits_precision()),
      denom_is_zero,
    )
    .resize_unchecked(num.bits_precision());
    let quotient = <_ as CtSelect>::ct_select(
      &num.checked_div(&denom).unwrap(),
      &BoxedUint::zero().resize_unchecked(num.bits_precision()),
      denom_is_zero,
    );
    quotient.resize_unchecked(denom_bits)
  }
}
