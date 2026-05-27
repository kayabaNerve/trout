use zeroize::Zeroize;

use crypto_bigint::{Choice, CtEq, CtSelect, BoxedUint};

#[derive(Clone, Debug)]
pub(super) struct Integer {
  pub(super) positive: Choice,
  value: BoxedUint,
}
impl Integer {
  pub(super) fn abs(&self) -> &BoxedUint {
    &self.value
  }
  pub(super) fn abs_mut(&mut self) -> &mut BoxedUint {
    &mut self.value
  }
  pub(super) fn into_abs(self) -> BoxedUint {
    self.value
  }
}
impl From<BoxedUint> for Integer {
  fn from(value: BoxedUint) -> Self {
    Integer { positive: 1.into(), value }
  }
}
impl CtEq for Integer {
  fn ct_eq(&self, b: &Self) -> Choice {
    self.positive.ct_eq(&b.positive) & self.value.ct_eq(&b.value)
  }
}
impl CtSelect for Integer {
  fn ct_select(&self, b: &Self, choice: Choice) -> Self {
    Self {
      positive: Choice::ct_select(&self.positive, &b.positive, choice),
      value: BoxedUint::ct_select(&self.value, &b.value, choice),
    }
  }
}
impl Zeroize for Integer {
  fn zeroize(&mut self) {
    self.positive = Choice::ct_select(&0.into(), &1.into(), 1.into());
    self.value.zeroize();
  }
}
