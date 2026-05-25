use crypto_bigint::{Choice, CtSelect, CtLt, Resize, Zero, ConcatenatingSquare, UintRef, BoxedUint};

impl super::c::Limbs for BoxedUint {
  #[inline(always)]
  fn widening_square(&self) -> (Self, Self) {
    let size = self.bits_precision();
    let square = self.concatenating_square().clone();
    let hi = (&square >> size).resize_unchecked(size);
    let lo = square.resize_unchecked(size);
    (lo, hi)
  }
  #[inline(always)]
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self {
    let denom_bits = denom.bits_precision();
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

impl super::reduction::Limbs for BoxedUint {
  #[inline(always)]
  fn like_zero(&self) -> Self {
    Zero::zero_like(self)
  }
  #[inline(always)]
  fn lt(&self, b: &Self, _limbs: usize) -> Choice {
    UintRef::new(self.as_ref()).ct_lt(UintRef::new(b.as_ref()))
  }
}
