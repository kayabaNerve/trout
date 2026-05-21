use crypto_bigint::{ConstZero, CheckedDiv, Concat, SplitEven, Limb, Uint};

use super::Limbs;

impl<const LIMBS: usize, const WIDE_LIMBS: usize> Limbs for Uint<LIMBS>
where
  Self: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
  Uint<WIDE_LIMBS>: CheckedDiv<Self> + SplitEven<Output = Self>,
{
  #[inline(always)]
  fn carrying_add(&self, b: &Self, carry: Limb) -> (Self, Limb) {
    self.carrying_add(b, carry)
  }
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
