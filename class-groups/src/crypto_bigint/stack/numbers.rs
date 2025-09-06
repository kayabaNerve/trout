use core::ops::{Add, Neg, Sub, Mul, Div, Rem};

use zeroize::Zeroize;

use crypto_bigint::{
  Choice, CtEq, CtSelect, ConcatenatingMul, Zero, One, NonZero, BitOps, Integer, Uint,
};
#[cfg(test)]
use crypto_bigint::U256;

pub(crate) fn mul_arbitrary_uints<
  const LHS_LIMBS: usize,
  const RHS_LIMBS: usize,
  const OUTPUT_LIMBS: usize,
>(
  a: Uint<LHS_LIMBS>,
  b: Uint<RHS_LIMBS>,
) -> Uint<OUTPUT_LIMBS> {
  let (c_lo, c_hi) = a.widening_mul(&b);
  let c_lo = c_lo.as_words();
  let c_hi = c_hi.as_words();
  let mut res = Uint::<{ OUTPUT_LIMBS }>::ZERO;
  res.as_mut_words()[.. c_lo.len()].copy_from_slice(c_lo);
  res.as_mut_words()[c_lo.len() ..].copy_from_slice(c_hi);
  res
}

// Calculate the difference of two `I`s, returning it and if `b` was greater.
//
// This assumes the difference will not have the top bit set.
fn difference<I: Copy + BitOps + Integer>(a: &I, b: &I) -> (I, Choice) {
  debug_assert!(!a.bit_vartime(a.bits_precision() - 1));
  let diff = a.wrapping_sub(b);
  let b_gt = Choice::from(diff.bit_vartime(diff.bits_precision() - 1) as u8);
  let diff = <_>::ct_select(&diff, &diff.wrapping_neg(), b_gt);
  (diff, b_gt)
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct IStruct<I: Copy + BitOps + Integer> {
  positive: Choice,
  value: I,
}
impl<I: Copy + BitOps + Integer> IStruct<I> {
  pub(crate) fn positive(&self) -> Choice {
    self.positive
  }
  pub(crate) fn abs(&self) -> &I {
    &self.value
  }
  pub(crate) fn into_abs(self) -> I {
    self.value
  }
  #[must_use]
  pub(crate) fn half(mut self) -> Self {
    self.value = self.value.overflowing_shr_vartime(1u32).unwrap();
    self.positive = Choice::ct_select(&self.positive, &1.into(), self.value.ct_eq(&I::zero()));
    self
  }

  pub(crate) fn one() -> Self {
    Self { positive: 1.into(), value: I::one() }
  }

  pub(crate) fn widen<I2: Copy + BitOps + Integer + From<(I, I)>>(self) -> IStruct<I2> {
    IStruct { positive: self.positive, value: I2::from((self.value, I::zero())) }
  }
}
impl<const LIMBS: usize> IStruct<Uint<LIMBS>> {
  pub(crate) fn mul_i_uint<const RHS_LIMBS: usize, const OUTPUT_LIMBS: usize>(
    self,
    other: IStruct<Uint<RHS_LIMBS>>,
  ) -> IStruct<Uint<OUTPUT_LIMBS>> {
    let value = mul_arbitrary_uints(self.value, other.value);
    // (positive * positive) | (negative * negative) | (0 * either)
    let positive = self.positive.ct_eq(&other.positive) | value.is_zero();
    IStruct { positive, value }
  }
}
impl<I: Copy + BitOps + Integer> From<I> for IStruct<I> {
  fn from(value: I) -> Self {
    IStruct { positive: 1.into(), value }
  }
}
impl<I: Copy + BitOps + Integer> Add<I> for IStruct<I> {
  type Output = IStruct<I>;
  fn add(self, other: I) -> IStruct<I> {
    let same_sign = IStruct { positive: self.positive, value: self.value + other };

    let other_positive = Choice::from(1);
    let (difference, other_is_greater) = difference(&self.value, &other);
    let greater_positive = Choice::ct_select(&self.positive, &other_positive, other_is_greater);
    // If they have different signs, the greater number's sign is preserved
    let not_same_sign = IStruct { positive: greater_positive, value: (difference) };

    IStruct::ct_select(&not_same_sign, &same_sign, self.positive.ct_eq(&other_positive))
  }
}
impl<I: Copy + BitOps + Integer> Add for IStruct<I> {
  type Output = IStruct<I>;
  fn add(self, other: Self) -> IStruct<I> {
    let same_sign = IStruct { positive: self.positive, value: self.value + other.value };

    let (difference, other_is_greater) = difference(&self.value, &other.value);
    let greater_positive = Choice::ct_select(&self.positive, &other.positive, other_is_greater);
    let not_same_sign = IStruct { positive: greater_positive, value: (difference) };

    IStruct::ct_select(&not_same_sign, &same_sign, self.positive.ct_eq(&other.positive))
  }
}
impl<I: Copy + BitOps + Integer> Sub for IStruct<I> {
  type Output = IStruct<I>;
  fn sub(self, other: Self) -> IStruct<I> {
    let sum = self.value.wrapping_add(&other.value);
    let (difference, other_is_greater) = difference(&self.value, &other.value);
    IStruct {
      positive: Choice::ct_select(&self.positive, &!other.positive, other_is_greater),
      value: I::ct_select(&sum, &(difference), self.positive.ct_eq(&other.positive)),
    }
  }
}
impl<I: Copy + BitOps + Integer> Neg for IStruct<I> {
  type Output = Self;
  fn neg(mut self) -> Self {
    // Perform the negation
    // self.sign = !self.sign;
    // If we had +0, preserve it as +0
    // self.sign = <_>::ct_select(&self.sign, &1.into(), self.value.ct_eq(&I::zero()));

    // Positive if zero or if prior negative, negative otherwise
    self.positive = <_>::ct_select(&0.into(), &1.into(), self.value.is_zero() | (!self.positive));
    self
  }
}

impl<IRhs: Integer, I: Copy + ConcatenatingMul<IRhs, Output: Copy + BitOps> + BitOps + Integer>
  Mul<IRhs> for IStruct<I>
{
  type Output = IStruct<<I as ConcatenatingMul<IRhs>>::Output>;
  fn mul(self, other: IRhs) -> Self::Output {
    let value = self.value.concatenating_mul(other);
    #[allow(clippy::suspicious_arithmetic_impl)]
    IStruct { positive: self.positive | value.is_zero(), value }
  }
}
impl<
  IRhs: Copy + BitOps + Integer,
  I: Copy + ConcatenatingMul<IRhs, Output: Copy + BitOps> + BitOps + Integer,
> Mul<IStruct<IRhs>> for IStruct<I>
{
  type Output = IStruct<<I as ConcatenatingMul<IRhs>>::Output>;
  fn mul(self, other: IStruct<IRhs>) -> Self::Output {
    let value = self.value.concatenating_mul(other.value);
    // (positive * positive) | (negative * negative) | (0 * either)
    #[allow(clippy::suspicious_arithmetic_impl)]
    let positive = self.positive.ct_eq(&other.positive) | value.is_zero();
    IStruct { positive, value }
  }
}

// These divisions are euclidean
impl<const LIMBS: usize> Div<Uint<LIMBS>> for IStruct<Uint<LIMBS>> {
  type Output = (IStruct<Uint<LIMBS>>, Uint<LIMBS>);
  fn div(self, denominator: Uint<LIMBS>) -> Self::Output {
    let (mut d, mut e) = self.value.div_rem(&NonZero::new(denominator).unwrap());

    let increment = (!self.positive) & (!e.is_zero());
    d = Uint::ct_select(&d, &(d + Uint::one()), increment);
    // Since we're dividing by an unsigned number, the sign inherits from the numerator
    let d = IStruct { positive: self.positive, value: d };
    e = Uint::ct_select(&e, &(denominator - e), increment);

    (d, e)
  }
}
impl<const LIMBS: usize> Div for IStruct<Uint<LIMBS>> {
  type Output = (IStruct<Uint<LIMBS>>, Uint<LIMBS>);
  fn div(self, denominator: Self) -> Self::Output {
    let (mut d, mut e) = self.value.div_rem(&NonZero::new(denominator.value).unwrap());

    let increment = (!self.positive) & (!e.is_zero());
    d = Uint::ct_select(&d, &(d + Uint::one()), increment);
    e = Uint::ct_select(&e, &(denominator.value - e), increment);

    // (positive * positive) | (negative * negative) | (0 / either)
    let d =
      IStruct { positive: self.positive.ct_eq(&denominator.positive) | d.is_zero(), value: d };
    (d, e)
  }
}
impl<I: Copy + Rem<Output = I> + BitOps + Integer> Rem<I> for IStruct<I> {
  type Output = I;
  fn rem(self, modulus: I) -> I {
    let rem = self.value % modulus;
    I::ct_select(&(modulus - rem), &rem, self.positive)
  }
}
impl<I: Copy + BitOps + Integer> CtEq for IStruct<I> {
  fn ct_eq(&self, b: &Self) -> Choice {
    self.positive.ct_eq(&b.positive) & self.value.ct_eq(&b.value)
  }
}
impl<I: Copy + BitOps + Integer> CtSelect for IStruct<I> {
  fn ct_select(&self, b: &Self, choice: Choice) -> Self {
    Self {
      positive: Choice::ct_select(&self.positive, &b.positive, choice),
      value: I::ct_select(&self.value, &b.value, choice),
    }
  }
}
impl<I: Copy + Zeroize + BitOps + Integer> Zeroize for IStruct<I> {
  fn zeroize(&mut self) {
    self.positive = Choice::ct_select(&0.into(), &1.into(), 1.into());
    self.value.zeroize();
  }
}

pub(crate) trait ExtendedGcd: Copy + Sized + BitOps + Integer {
  // (g, u, other / g)
  fn extended_gcd_part(self, other: Self) -> (Self, Self, Self);
  // (g, u, v, self / g)
  fn extended_gcd(self, other: Self) -> (Self, Self, IStruct<Self>, Self);
}
impl<const LIMBS: usize> ExtendedGcd for Uint<LIMBS> {
  fn extended_gcd_part(self, other: Self) -> (Self, Self, Self) {
    debug_assert!(bool::from((!self.ct_eq(&Self::zero())) | (!other.ct_eq(&Self::zero()))));

    let res = self.xgcd(&other);
    debug_assert!(!bool::from(res.x.is_negative() & res.y.is_negative()));
    let g = res.gcd;
    let u = res.x;
    let other_div_g = res.rhs_on_gcd;

    let u_abs = u.abs();
    let u = <_>::ct_select(&u_abs, &other_div_g.saturating_sub(&u_abs), u.is_negative());

    (g, u, other_div_g)
  }

  fn extended_gcd(self, other: Self) -> (Self, Self, IStruct<Self>, Self) {
    debug_assert!(bool::from((!self.ct_eq(&Self::zero())) | (!other.ct_eq(&Self::zero()))));

    let res = self.xgcd(&other);
    debug_assert!(!bool::from(res.x.is_negative() & res.y.is_negative()));
    let g = res.gcd;
    let u = res.x;
    let v = res.y;
    let self_div_g = res.lhs_on_gcd;
    let other_div_g = res.rhs_on_gcd;

    let u_is_neg = u.is_negative();
    let u_abs = u.abs();
    let u = <_>::ct_select(&u_abs, &other_div_g.saturating_sub(&u_abs), u_is_neg);

    let v_is_neg = v.is_negative();
    let v_abs = v.abs();
    let v_abs = <_>::ct_select(&v_abs, &self_div_g.saturating_sub(&v_abs), u_is_neg);
    let v = IStruct::from(v_abs);
    // Restore the sign `v` originally had
    let v = <_>::ct_select(&v, &-v, v_is_neg);
    // If we negated `u`, negate `v`
    let v = <_>::ct_select(&v, &-v, u_is_neg);

    (g, u, v, self_div_g)
  }
}

#[test]
fn test_integer_sub() {
  // Positive minus smaller positive
  {
    let res = IStruct::from(U256::from(2u8)) - IStruct::from(U256::ONE);
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::ONE)));
  }
  // Positive minus smaller negative
  {
    let res = IStruct::from(U256::from(2u8)) - -IStruct::from(U256::ONE);
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(3u8))));
  }
  // Positive minus larger positive
  {
    let res = IStruct::from(U256::from(2u8)) - IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::ONE)));
  }
  // Positive minus larger negative
  {
    let res = IStruct::from(U256::from(2u8)) - -IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(5u8))));
  }
  // Negative minus smaller positive
  {
    let res = -IStruct::from(U256::from(2u8)) - IStruct::from(U256::ONE);
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(3u8))));
  }
  // Negative minus smaller negative
  {
    let res = -IStruct::from(U256::from(2u8)) - -IStruct::from(U256::ONE);
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::ONE)));
  }
  // Negative minus larger positive
  {
    let res = -IStruct::from(U256::from(2u8)) - IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(5u8))));
  }
  // Negative minus larger negative
  {
    let res = -IStruct::from(U256::from(2u8)) - -IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::ONE)));
  }
}

#[test]
fn test_integer_div() {
  let two = IStruct::from(U256::from(2u8));
  let neg_two = -two;
  let three = U256::from(3u8);

  {
    let (res, rem) = two / three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::ZERO);
    assert_eq!(rem, two.value);
  }
  {
    let (res, rem) = -IStruct::from(U256::from(6u8)) / three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value, U256::from(2u8));
    assert_eq!(rem, U256::ZERO);
  }
  {
    let (res, rem) = neg_two / three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value, U256::ONE);
    assert_eq!(rem, U256::ONE);
  }

  let three = IStruct::from(three);
  {
    let (res, rem) = two / three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::ZERO);
    assert_eq!(rem, two.value);
  }
  {
    let (res, rem) = neg_two / three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value, U256::ONE);
    assert_eq!(rem, U256::ONE);
  }

  let neg_three = -three;
  {
    let (res, rem) = two / neg_three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::ZERO);
    assert_eq!(rem, two.value);
  }
  {
    let (res, rem) = neg_two / neg_three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::ONE);
    assert_eq!(rem, U256::ONE);
  }
}

#[test]
fn gcd() {
  // Ensure the underlying crypto-bigint handles the case where one is zero correctly
  assert_eq!(U256::ONE.gcd(&U256::ZERO), U256::ONE);

  {
    let (gcd, u, v, _) = U256::ONE.extended_gcd(U256::ZERO);
    assert_eq!(gcd, U256::ONE);
    assert_eq!(u, U256::ONE);
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::ZERO);
  }

  {
    let (gcd, u, v, _) = U256::ZERO.extended_gcd(U256::ONE);
    assert_eq!(gcd, U256::ONE);
    assert_eq!(u, U256::ZERO);
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::ONE);
  }

  {
    let (gcd, u, v, _) = U256::from(2u8).extended_gcd(U256::from(3u8));
    assert_eq!(gcd, U256::ONE);
    assert_eq!(u, U256::from(2u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value, U256::ONE);
  }

  {
    let (gcd, u, v, _) = (U256::from(4u8)).extended_gcd(U256::from(8u8));
    assert_eq!(gcd, U256::from(4u8));
    assert_eq!(u, U256::ONE);
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::ZERO);
  }

  {
    let (gcd, u, v, _) = (U256::from(8u8)).extended_gcd(U256::from(4u8));
    assert_eq!(gcd, U256::from(4u8));
    assert_eq!(u, U256::ZERO);
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::ONE);
  }

  {
    let (gcd, u, v, _) = (U256::from(4u8)).extended_gcd(U256::from(10u8));
    assert_eq!(gcd, U256::from(2u8));
    assert_eq!(u, U256::from(3u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value, U256::ONE);
  }

  {
    let (gcd, u, v, _) = U256::from(2u8).extended_gcd(U256::from(2u8));
    assert_eq!(gcd, U256::from(2u8));
    assert_eq!(u, U256::ONE);
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::ZERO);
  }

  {
    let (gcd, u, v, _) = (U256::from(10u8)).extended_gcd(U256::from(4u8));
    assert_eq!(gcd, U256::from(2u8));
    assert_eq!(u, U256::from(1u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value, U256::from(2u8));
  }

  {
    let a = crypto_bigint::U512::from_be_hex(concat!(
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000000000000000000000000000001A0DEEF6F3AC2566149D925044"
    ));
    let b = crypto_bigint::U512::from_be_hex(concat!(
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000072B69C9DD0AA15F135675EA9C5180CF8FF0A59298CFC92E87FA"
    ));
    let (gcd, u, v, _) = a.extended_gcd(b);
    // u * a + v * b = g
    // v is either 0 or negative, so this is equivalent to
    // u * a - |v| * b = g
    // which is equivalent to
    // u * a = g + |v| * b
    assert_eq!(u * a, gcd + (v.value * b));
  }
}
