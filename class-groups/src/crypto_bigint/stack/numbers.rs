use core::ops::{Add, Neg, Sub};

use zeroize::Zeroize;

use crypto_bigint::{Choice, CtEq, CtSelect, BitOps, Integer};
#[cfg(test)]
use crypto_bigint::U256;

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
  #[must_use]
  pub(crate) fn half(mut self) -> Self {
    self.value = self.value.overflowing_shr_vartime(1u32).unwrap();
    self.positive = Choice::ct_select(&self.positive, &1.into(), self.value.ct_eq(&I::zero()));
    self
  }
  #[must_use]
  pub(crate) fn ct_neg(mut self, neg: Choice) -> Self {
    self.positive = <_>::ct_select(&self.positive, &!self.positive, neg);
    self
  }
}
impl<I: Copy + BitOps + Integer> From<I> for IStruct<I> {
  fn from(value: I) -> Self {
    IStruct { positive: 1.into(), value }
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
