use crypto_bigint::{Concat, SplitEven, NonZero, Uint};

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
    let quotient = concatenated / *denom;
    quotient.split().0
  }
}

impl<const LIMBS: usize> super::reduction::Limbs for Uint<LIMBS> {
  #[inline(always)]
  fn like_zero(&self) -> Self {
    Self::ZERO
  }
}

impl<const LIMBS: usize, const WIDE_LIMBS: usize> super::composition::Limbs for Uint<LIMBS>
where
  Self: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
  Uint<WIDE_LIMBS>: SplitEven<Output = Self>,
{
  type Wide = <Self as Concat<LIMBS>>::Output;
  #[expect(private_interfaces)]
  fn xgcd(self, other: Self) -> super::composition::Xgcd<Self> {
    let xgcd = Uint::xgcd(&self, &other);
    super::composition::Xgcd {
      d: xgcd.gcd,
      u: (xgcd.x.is_positive(), xgcd.x.abs()),
      v: (xgcd.y.is_positive(), xgcd.y.abs()),
    }
  }
  fn div(self, denom: &Self) -> Self {
    self.div_rem(&NonZero::new(*denom).unwrap()).0
  }
  fn mul_mod(&self, other: &Self, modulus: &Self) -> Self {
    self.mul_mod(other, &NonZero::new(*modulus).unwrap())
  }
  fn mul(&self, other: &Self) -> Self::Wide {
    self.concatenating_mul(other)
  }
  fn square(&self) -> Self::Wide {
    self.concatenating_square()
  }
}

impl<const LIMBS: usize, const WIDE_LIMBS: usize>
  super::composition::WideLimbs<<Self as SplitEven>::Output> for Uint<WIDE_LIMBS>
where
  Uint<WIDE_LIMBS>: SplitEven<Output = Uint<LIMBS>>,
{
  fn rem(self, denom: &<Self as SplitEven>::Output) -> <Self as SplitEven>::Output {
    self.div_rem(&NonZero::new(*denom).unwrap()).1
  }
}
