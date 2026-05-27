use zeroize::Zeroize;

use crypto_bigint::{Choice, CtEq, CtSelect, BitOps, Integer};

#[derive(Clone, Copy, Debug)]
pub(crate) struct IStruct<I: Copy + BitOps + Integer> {
  pub(super) positive: Choice,
  value: I,
}
impl<I: Copy + BitOps + Integer> IStruct<I> {
  pub(crate) fn abs(&self) -> &I {
    &self.value
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
