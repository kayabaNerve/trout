#![expect(clippy::inline_always)]

use crypto_bigint::{Choice, CtEq as _, Encoding, Concat, SplitEven, One as _, NonZero, Uint};

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
  #[inline(always)]
  fn rem(num: Self, denom: &Self) -> Self {
    num.div_rem(&NonZero::new(*denom).unwrap()).1
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
  #[inline(always)]
  fn div_exact(self, denom: &Self) -> Self {
    self.div_rem(&NonZero::new(*denom).unwrap()).0
  }
  #[inline(always)]
  fn mul_mod(&self, other: &Self, modulus: &Self) -> Self {
    self.mul_mod(other, &NonZero::new(*modulus).unwrap())
  }
  #[inline(always)]
  fn mul(&self, other: &Self) -> Self::Wide {
    self.concatenating_mul(other)
  }
  #[inline(always)]
  fn square(&self) -> Self::Wide {
    self.concatenating_square()
  }
}

impl<const LIMBS: usize, const WIDE_LIMBS: usize>
  super::composition::WideLimbs<<Self as SplitEven>::Output> for Uint<WIDE_LIMBS>
where
  Uint<WIDE_LIMBS>: SplitEven<Output = Uint<LIMBS>>,
{
  #[inline(always)]
  fn rem(self, denom: &<Self as SplitEven>::Output) -> <Self as SplitEven>::Output {
    self.div_rem(&NonZero::new(*denom).unwrap()).1
  }
}

struct StitchedBytes<const WIDE_LIMBS: usize>
where
  Uint<WIDE_LIMBS>: Encoding,
{
  buf: <Uint<WIDE_LIMBS> as Encoding>::Repr,
  len: usize,
}

impl<const WIDE_LIMBS: usize> AsRef<[u8]> for StitchedBytes<WIDE_LIMBS>
where
  Uint<WIDE_LIMBS>: Encoding,
{
  fn as_ref(&self) -> &[u8] {
    &self.buf.as_ref()[.. self.len]
  }
}

impl<const LIMBS: usize, const WIDE_LIMBS: usize> super::encoding::Limbs for Uint<LIMBS>
where
  Self: Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
  Uint<WIDE_LIMBS>: SplitEven<Output = Self>,
{
  fn wide_div_rem_thin(wide: Self::Wide, thin: &NonZero<Self>) -> (Self::Wide, Self) {
    wide.div_rem(thin)
  }

  fn coprime(a: Self, b_abs: Self, c: Self::Wide) -> Choice {
    a.gcd(&b_abs).concat(&Self::ZERO).gcd(&c).is_one()
  }
}

impl<const LIMBS: usize, const WIDE_LIMBS: usize> super::element::Limbs for Uint<LIMBS>
where
  Self: Encoding<Repr: Default> + Concat<LIMBS, Output = Uint<WIDE_LIMBS>>,
  Uint<WIDE_LIMBS>: Encoding<Repr: Default> + SplitEven<Output = Self> + super::c::Limbs,
{
  type Bytes = crypto_bigint::EncodedUint<LIMBS>;

  #[inline(always)]
  fn max_bits() -> Option<u32> {
    Some(Self::BITS)
  }

  #[inline(always)]
  fn truncate(wide: Self::Wide, _bits: u32) -> Self {
    wide.split().0
  }
  #[inline(always)]
  fn widen(thin: Self, _wide_bits: u32) -> Self::Wide {
    thin.concat(&Uint::ZERO)
  }

  #[inline(always)]
  fn to_le_bytes(self) -> Self::Bytes {
    Self::to_le_bytes(&self)
  }
  #[inline(always)]
  fn wide_to_le_bytes(wide: Self::Wide) -> impl AsRef<[u8]> {
    Self::Wide::to_le_bytes(&wide)
  }

  #[inline(always)]
  fn from_le_slice(bytes: &[u8], max_bits: u32) -> Self {
    assert!(max_bits <= Self::BITS);

    let mut fixed_bytes = <Self as Encoding>::Repr::default();
    {
      let fixed_bytes = fixed_bytes.as_mut();
      let mutual_len = fixed_bytes.len().min(bytes.len());
      for b in bytes.iter().skip(mutual_len) {
        assert!(bool::from(b.ct_eq(&0)));
      }
      fixed_bytes[.. mutual_len].copy_from_slice(&bytes[.. mutual_len]);
    }

    Self::from_le_bytes(fixed_bytes)
  }
  #[inline(always)]
  fn wide_from_le_slice(bytes: &[u8], max_bits: u32) -> Self::Wide {
    assert!(max_bits <= Self::Wide::BITS);

    let mut fixed_bytes = <Uint<WIDE_LIMBS> as Encoding>::Repr::default();
    {
      let fixed_bytes = fixed_bytes.as_mut();
      let mutual_len = fixed_bytes.len().min(bytes.len());
      for b in bytes.iter().skip(mutual_len) {
        assert!(bool::from(b.ct_eq(&0)));
      }
      fixed_bytes[.. mutual_len].copy_from_slice(&bytes[.. mutual_len]);
    }

    Self::Wide::from_le_bytes(fixed_bytes)
  }

  fn stitch(first: Self::Bytes, second: Self::Bytes, bytes_per_element: usize) -> impl AsRef<[u8]> {
    let mut buf = <Self::Wide as Encoding>::Repr::default();
    buf.as_mut()[.. bytes_per_element].copy_from_slice(&first.as_ref()[.. bytes_per_element]);
    buf.as_mut()[bytes_per_element .. (2 * bytes_per_element)]
      .copy_from_slice(&second.as_ref()[.. bytes_per_element]);
    StitchedBytes::<WIDE_LIMBS> { buf, len: 2 * bytes_per_element }
  }
}
