use crypto_bigint::{ConstZero, Concat, SplitEven, Uint};

impl<const LIMBS: usize, const WIDE_LIMBS: usize> super::c::Limbs for Uint<LIMBS>
where
  Self: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
  Uint<WIDE_LIMBS>: SplitEven<Output = Self>,
{
  #[inline(always)]
  fn widening_square(&self) -> (Self, Self) {
    Uint::<LIMBS>::widening_square(self)
  }
  #[inline(always)]
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self {
    let concatenated = num.0.concat(&num.1);
    let quotient = concatenated
      .checked_div(denom)
      .unwrap_or(<<Self as Concat<LIMBS>>::Output as ConstZero>::ZERO);
    quotient.split().0
  }
}

impl<const LIMBS: usize> super::reduction::Limbs for Uint<LIMBS> {
  #[inline(always)]
  fn like_zero(&self) -> Self {
    Self::ZERO
  }
}
