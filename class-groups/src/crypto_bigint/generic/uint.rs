use crypto_bigint::{Encoding, Concat, SplitEven, NonZero, Uint};

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

impl<const LIMBS: usize, const WIDE_LIMBS: usize> super::element::Limbs for Uint<LIMBS>
where
  Self: Encoding<Repr: Default> + Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
  Uint<WIDE_LIMBS>: Encoding<Repr: Default> + SplitEven<Output = Self> + super::c::Limbs,
{
  fn max_bits() -> Option<u32> {
    Some(Self::BITS)
  }

  fn truncate(wide: Self::Wide, _bits: u32) -> Self {
    wide.split().0
  }
  fn widen(thin: Self, _wide_bits: u32) -> Self::Wide {
    thin.concat(&Uint::ZERO)
  }

  fn to_be_bytes(self) -> impl AsRef<[u8]> {
    Self::to_be_bytes(&self)
  }

  fn from_be_slice(mut bytes: &[u8], _max_bits: u32) -> Self {
    while bytes.first() == Some(&0) {
      bytes = &bytes[1 ..];
    }

    let mut fixed_bytes = <Self as Encoding>::Repr::default();
    fixed_bytes.as_mut()[(Self::BYTES - bytes.len()) ..].copy_from_slice(bytes);

    Self::from_be_bytes(fixed_bytes)
  }

  fn wide_from_be_slice(mut bytes: &[u8], _max_bits: u32) -> Self::Wide {
    while bytes.first() == Some(&0) {
      bytes = &bytes[1 ..];
    }

    let mut fixed_bytes = <Uint<WIDE_LIMBS> as Encoding>::Repr::default();
    fixed_bytes.as_mut()[(Uint::<WIDE_LIMBS>::BYTES - bytes.len()) ..].copy_from_slice(bytes);

    Self::Wide::from_be_bytes(fixed_bytes)
  }
}
