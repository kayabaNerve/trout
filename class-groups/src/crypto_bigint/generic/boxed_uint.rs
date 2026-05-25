use crypto_bigint::{Resize, Zero, ConcatenatingSquare, BoxedUint};

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
    // The caller is bound to not pass `0` as the denominator
    let quotient = num / denom.to_nz().unwrap();
    quotient.resize_unchecked(denom_bits)
  }
}

impl super::reduction::Limbs for BoxedUint {
  #[inline(always)]
  fn like_zero(&self) -> Self {
    Zero::zero_like(self)
  }
}
