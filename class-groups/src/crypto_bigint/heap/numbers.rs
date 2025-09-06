// This file contains the necessary wrappers around `BoxedUint` as necessary for
// `CryptoBigintElement`

use core::ops::{Add, Neg, Sub, Mul, Div, Rem, Shl, Shr};

use zeroize::Zeroize;

use crypto_bigint::{
  Choice, CtEq, CtSelect, CtLt, CtGt, NonZero, Resize, ConcatenatingMul, Gcd, BoxedUint,
};

enum Cow<'a, B> {
  Borrowed(&'a B),
  Owned(B),
}

impl<'a, B: Clone> Cow<'a, B> {
  fn as_ref(&self) -> &B {
    match self {
      Cow::Borrowed(borrow) => borrow,
      Cow::Owned(value) => value,
    }
  }

  fn take(self) -> B {
    match self {
      Cow::Borrowed(borrow) => borrow.clone(),
      Cow::Owned(value) => value,
    }
  }
}

fn resize<'a>(a: &'a BoxedUint, b: &'a BoxedUint) -> (Cow<'a, BoxedUint>, Cow<'a, BoxedUint>) {
  let a_precision = a.bits_precision();
  let b_precision = b.bits_precision();
  let precision = a_precision.max(b_precision);
  let a = if a_precision < precision {
    Cow::Owned(a.resize_unchecked(precision))
  } else {
    Cow::Borrowed(a)
  };
  let b = if b_precision < precision {
    Cow::Owned(b.resize_unchecked(precision))
  } else {
    Cow::Borrowed(b)
  };
  (a, b)
}

// ct_select panics if the operands have different lengths
fn boxed_uint_ct_select(a: &BoxedUint, b: &BoxedUint, choice: Choice) -> BoxedUint {
  let precision = a.bits_precision().max(b.bits_precision());
  BoxedUint::ct_select(&a.resize_unchecked(precision), &b.resize_unchecked(precision), choice)
}

// div_rem panics if the operands have different lengths
fn boxed_uint_div_rem(numerator: &BoxedUint, denominator: &BoxedUint) -> (BoxedUint, BoxedUint) {
  let denominator_bits = denominator.bits_precision();
  let (numerator, denominator) = resize(numerator, denominator);
  let (d, e) = numerator.as_ref().div_rem(&NonZero::new(denominator.take()).unwrap());
  // Since we know the bound on the denominator, we can reduce the remainder
  let e = e.resize(denominator_bits);
  (d, e)
}

fn boxed_uint_div(numerator: &BoxedUint, denominator: &BoxedUint) -> BoxedUint {
  boxed_uint_div_rem(numerator, denominator).0
}

// Calculate the difference of two `BoxedUint`s, returning it and if `b` was greater
fn difference(a: &BoxedUint, b: &BoxedUint) -> (BoxedUint, Choice) {
  let b_is_greater = b.ct_gt(a);
  // These may contain equivalent values which is fine for this
  let greater = boxed_uint_ct_select(a, b, b_is_greater);
  let lesser = boxed_uint_ct_select(a, b, !b_is_greater);
  let difference = greater - lesser;
  (difference, b_is_greater)
}

/// A constant-time variable-size (dynamically-allocated) unsigned integer.
#[derive(Clone, Debug, Zeroize)]
pub(crate) struct UnsignedInteger(pub(crate) BoxedUint);

impl From<BoxedUint> for UnsignedInteger {
  fn from(value: BoxedUint) -> Self {
    Self(value)
  }
}

impl UnsignedInteger {
  #[must_use]
  pub(crate) fn to_be_bytes(&self) -> Vec<u8> {
    self.0.to_be_bytes().into()
  }

  #[must_use]
  pub(crate) fn from_be_slice(slice: &[u8]) -> Self {
    Self(BoxedUint::from_be_slice(slice, u32::try_from(slice.len() * 8).unwrap()).unwrap())
  }

  pub(crate) fn resize(&mut self, bits: u32) {
    self.0 = self.0.clone().resize_unchecked(bits.max(self.0.bits_precision()));
  }

  pub(crate) fn is_zero(&self) -> Choice {
    self.0.is_zero()
  }
  pub(crate) fn is_one(&self) -> Choice {
    self.0.is_one()
  }
}

impl Add for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn add(self, other: Self) -> UnsignedInteger {
    UnsignedInteger(self.0.concatenating_add(&other.0))
  }
}
impl Mul for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn mul(self, other: Self) -> UnsignedInteger {
    let res = UnsignedInteger(self.0.concatenating_mul(&other.0));
    debug_assert_eq!(res.0.bits_precision(), self.0.bits_precision() + other.0.bits_precision());
    res
  }
}
impl Div for &UnsignedInteger {
  type Output = (UnsignedInteger, UnsignedInteger);
  fn div(self, denominator: Self) -> Self::Output {
    let (d, e) = boxed_uint_div_rem(&self.0, &denominator.0);
    (UnsignedInteger(d), UnsignedInteger(e))
  }
}
impl Rem for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn rem(self, modulus: Self) -> UnsignedInteger {
    let modulus_bits = modulus.0.bits_precision();
    let precision = self.0.bits_precision().max(modulus_bits);

    let value = self.0.clone().resize_unchecked(precision);
    let modulus = NonZero::new(modulus.0.clone().resize_unchecked(precision)).unwrap();
    let rem = value % modulus;

    UnsignedInteger(rem.resize_unchecked(modulus_bits))
  }
}
impl Shl<u32> for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn shl(self, shift: u32) -> UnsignedInteger {
    // widen this to ensure it doesn't overflow
    let new_precision = self.0.bits_precision() + shift;
    UnsignedInteger(self.0.clone().resize_unchecked(new_precision) << shift)
  }
}
impl Shr<u32> for UnsignedInteger {
  type Output = UnsignedInteger;
  fn shr(self, shift: u32) -> UnsignedInteger {
    UnsignedInteger(self.0 >> shift)
  }
}
impl CtEq for UnsignedInteger {
  fn ct_eq(&self, b: &Self) -> Choice {
    self.0.ct_eq(&b.0)
  }
}
impl CtLt for UnsignedInteger {
  fn ct_lt(&self, b: &Self) -> Choice {
    self.0.ct_lt(&b.0)
  }
}
impl CtGt for UnsignedInteger {
  fn ct_gt(&self, b: &Self) -> Choice {
    self.0.ct_gt(&b.0)
  }
}
impl CtSelect for UnsignedInteger {
  fn ct_select(&self, b: &Self, choice: Choice) -> Self {
    Self(boxed_uint_ct_select(&self.0, &b.0, choice))
  }
}

#[derive(Clone, Debug)]
pub(crate) struct Integer {
  positive: Choice,
  value: UnsignedInteger,
}
impl Integer {
  pub(crate) fn positive(&self) -> Choice {
    self.positive
  }
  pub(crate) fn abs(&self) -> &UnsignedInteger {
    &self.value
  }
  pub(crate) fn abs_mut(&mut self) -> &mut UnsignedInteger {
    &mut self.value
  }
  pub(crate) fn into_abs(self) -> UnsignedInteger {
    self.value
  }
  #[must_use]
  pub(crate) fn half(mut self) -> Integer {
    self.value = self.value >> 1;
    self.positive = Choice::ct_select(&self.positive, &1.into(), self.value.is_zero());
    self
  }
}
impl From<UnsignedInteger> for Integer {
  fn from(value: UnsignedInteger) -> Self {
    Integer { positive: 1.into(), value }
  }
}
impl Add<&UnsignedInteger> for &Integer {
  type Output = Integer;
  fn add(self, other: &UnsignedInteger) -> Integer {
    let same_sign = Integer { positive: self.positive, value: &self.value + other };

    let other_positive = Choice::from(1);
    let (difference, other_is_greater) = difference(&self.value.0, &other.0);
    let greater_positive = Choice::ct_select(&self.positive, &other_positive, other_is_greater);
    // If they have different signs, the greater number's sign is preserved
    let not_same_sign = Integer { positive: greater_positive, value: UnsignedInteger(difference) };

    CtSelect::ct_select(&not_same_sign, &same_sign, self.positive.ct_eq(&other_positive))
  }
}
impl Add for &Integer {
  type Output = Integer;
  fn add(self, other: Self) -> Integer {
    let same_sign = Integer { positive: self.positive, value: &self.value + &other.value };

    let (difference, other_is_greater) = difference(&self.value.0, &other.value.0);
    let greater_positive = Choice::ct_select(&self.positive, &other.positive, other_is_greater);
    let not_same_sign = Integer { positive: greater_positive, value: UnsignedInteger(difference) };

    CtSelect::ct_select(&not_same_sign, &same_sign, self.positive.ct_eq(&other.positive))
  }
}
impl Sub for &Integer {
  type Output = Integer;
  fn sub(self, other: Self) -> Integer {
    let sum = &self.value + &other.value;
    let (difference, other_is_greater) = difference(&self.value.0, &other.value.0);
    Integer {
      positive: Choice::ct_select(&self.positive, &!other.positive, other_is_greater),
      value: UnsignedInteger::ct_select(
        &sum,
        &UnsignedInteger(difference),
        self.positive.ct_eq(&other.positive),
      ),
    }
  }
}
impl Neg for Integer {
  type Output = Self;
  fn neg(mut self) -> Self {
    // Perform the negation
    // self.sign = !self.sign;
    // If we had +0, preserve it as +0
    // self.sign = <_>::ct_select(&self.sign, &1.into(), self.value.is_zero());

    // Positive if zero or if prior negative, negative otherwise
    self.positive = <_>::ct_select(&0.into(), &1.into(), self.value.0.is_zero() | (!self.positive));
    self
  }
}
impl Mul<&UnsignedInteger> for &Integer {
  type Output = Integer;
  fn mul(self, other: &UnsignedInteger) -> Integer {
    let value = &self.value * other;
    Integer { positive: self.positive | value.0.is_zero(), value }
  }
}
impl Mul for &Integer {
  type Output = Integer;
  fn mul(self, other: Self) -> Integer {
    let value = &self.value * &other.value;
    // (positive * positive) | (negative * negative) | (0 * either)
    let positive = self.positive.ct_eq(&other.positive) | value.0.is_zero();
    Integer { positive, value }
  }
}
// These divisions are euclidean
impl Div<&UnsignedInteger> for &Integer {
  type Output = (Integer, UnsignedInteger);
  fn div(self, denominator: &UnsignedInteger) -> Self::Output {
    let (mut d, mut e) = &self.value / denominator;

    let increment = (!self.positive) & (!e.is_zero());
    d = UnsignedInteger::ct_select(&d, &(&d + &UnsignedInteger(BoxedUint::one())), increment);
    // Since we're dividing by an unsigned number, the sign inherits from the numerator
    let d = Integer { positive: self.positive, value: d };
    e = UnsignedInteger::ct_select(&e, &UnsignedInteger(&denominator.0 - &e.0), increment);

    {
      let recovered = &(&d * denominator) + &e;
      debug_assert!(bool::from(recovered.positive.ct_eq(&self.positive)));
      debug_assert_eq!(recovered.value.0, self.value.0);
    }

    (d, e)
  }
}
impl Div for &Integer {
  type Output = (Integer, UnsignedInteger);
  fn div(self, denominator: Self) -> Self::Output {
    let (mut d, mut e) = &self.value / &denominator.value;

    let increment = (!self.positive) & (!e.is_zero());
    d = UnsignedInteger::ct_select(&d, &(&d + &UnsignedInteger(BoxedUint::one())), increment);
    e = UnsignedInteger::ct_select(&e, &UnsignedInteger(&denominator.value.0 - &e.0), increment);

    // (positive * positive) | (negative * negative) | (0 / either)
    let d =
      Integer { positive: self.positive.ct_eq(&denominator.positive) | d.0.is_zero(), value: d };
    {
      let recovered = &(&d * denominator) + &e;
      debug_assert!(bool::from(recovered.positive.ct_eq(&self.positive)));
      debug_assert_eq!(recovered.value.0, self.value.0);
    }
    (d, e)
  }
}
impl Rem<&UnsignedInteger> for &Integer {
  type Output = UnsignedInteger;
  fn rem(self, modulus: &UnsignedInteger) -> UnsignedInteger {
    let rem = &self.value % modulus;
    let rem = boxed_uint_ct_select(&(&modulus.0 - &rem.0), &rem.0, self.positive);
    UnsignedInteger(rem)
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
      value: UnsignedInteger::ct_select(&self.value, &b.value, choice),
    }
  }
}
impl Zeroize for Integer {
  fn zeroize(&mut self) {
    self.positive = Choice::ct_select(&0.into(), &1.into(), 1.into());
    self.value.zeroize();
  }
}

impl UnsignedInteger {
  pub(crate) fn gcd(&self, other: &Self) -> UnsignedInteger {
    let self_precision = self.0.bits_precision();
    let other_precision = other.0.bits_precision();
    let self_is_zero = self.is_zero();
    // Choose the precision of the non-zero element
    let precision = u32::ct_select(&self_precision, &other_precision, self_is_zero);
    // Choose the smallest precision of both elements if both are non-zero
    let precision = u32::ct_select(
      &precision,
      &self_precision.min(other_precision),
      (!self_is_zero) & (!other.is_zero()),
    );

    let (a, b) = resize(&self.0, &other.0);
    // Calculate the gcd via the method provided by crypto-bigint
    let gcd = a.as_ref().gcd(b.as_ref());
    UnsignedInteger(gcd.resize_unchecked(precision))
  }

  pub(crate) fn extended_gcd_part(&self, other: &Self) -> (UnsignedInteger, UnsignedInteger) {
    debug_assert!(bool::from((!self.0.is_zero()) | (!other.0.is_zero())));

    let a = &self.0;
    let b = &other.0;
    let gcd = self.gcd(other).0;

    let a_is_zero = a.is_zero();
    let b_is_zero = b.is_zero();
    let a_eq_b = a.ct_eq(b);
    let special_case = a_is_zero | b_is_zero | a_eq_b;

    // Calculate the multiplicative inverse of `(a / g) % (b / g)`, which is `u`
    let u = |a: BoxedUint, b: BoxedUint, gcd: BoxedUint| {
      let a_div_g = boxed_uint_div(&a, &gcd);
      let b_div_g = boxed_uint_div(&b, &gcd);

      let a_div_g = (&UnsignedInteger(a_div_g) % &UnsignedInteger(b_div_g.clone())).0;
      UnsignedInteger(
        a_div_g
          .invert_mod(&NonZero::new(b_div_g).unwrap())
          // Happens when `a` is a multiple of `b`
          .unwrap_or(BoxedUint::zero_with_precision(a_div_g.bits_precision())),
      )
    };

    // Call with `a, b, gcd` if not a special case and `1, 2, 1` if a special case
    let u = u(
      boxed_uint_ct_select(a, &BoxedUint::one(), special_case),
      boxed_uint_ct_select(b, &BoxedUint::from(2u8), special_case),
      boxed_uint_ct_select(&gcd, &BoxedUint::one(), special_case),
    );

    // Correct for the cases `a == 0`, `b == 0`
    let u = UnsignedInteger::ct_select(&u, &UnsignedInteger(BoxedUint::zero()), a_is_zero);
    let u = UnsignedInteger::ct_select(&u, &UnsignedInteger(BoxedUint::one()), b_is_zero);

    // Correct for the case `a == b`
    let u = UnsignedInteger::ct_select(&u, &UnsignedInteger(BoxedUint::one()), a_eq_b);

    let gcd = UnsignedInteger(gcd);
    (gcd, u)
  }

  pub(crate) fn extended_gcd(&self, other: &Self) -> (UnsignedInteger, UnsignedInteger, Integer) {
    debug_assert!(bool::from((!self.0.is_zero()) | (!other.0.is_zero())));

    let (gcd, u) = self.extended_gcd_part(other);
    let gcd = gcd.0;
    let a = &self.0;
    let b = &other.0;

    let b_is_zero = b.is_zero();

    // Calculate `v` for `ua + vb = g`
    let v = |b: BoxedUint| {
      let ua = u.0.concatenating_mul(&a);
      let (difference, _gcd_is_greater) = difference(&ua, &gcd);
      let (v, rem) = boxed_uint_div_rem(&difference, &b);
      debug_assert!(bool::from(rem.is_zero()));

      let v = Integer::from(UnsignedInteger(v));
      // We prefer `u` to be positive and `v` to be negative, yet `v` will be positive if `u` is
      // zero
      // TODO: ct_neg
      Integer::ct_select(&v, &-v.clone(), !u.is_zero())
    };

    // Call with `b` if not a special case and `1` if `b == 0`
    let v = v(boxed_uint_ct_select(b, &BoxedUint::one(), b_is_zero));

    // Correct for the case `b == 0`
    let v = Integer::ct_select(&v, &Integer::from(UnsignedInteger(BoxedUint::zero())), b_is_zero);

    let gcd = UnsignedInteger(gcd);

    {
      let recovered = &Integer::from(self * &u) + &(&v * other);
      debug_assert!(bool::from(recovered.positive));
      debug_assert_eq!(recovered.value.0, gcd.0);
      debug_assert!(bool::from((!u.0.ct_gt(&boxed_uint_div(b, &gcd.0))) | b_is_zero));
      debug_assert!(bool::from((!v.value.0.ct_gt(&boxed_uint_div(a, &gcd.0))) | a.is_zero()));
    }

    (gcd, u, v)
  }
}

#[test]
fn test_integer_sub() {
  // Positive minus smaller positive
  {
    let res = &Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &Integer::from(UnsignedInteger(BoxedUint::one()));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::one())));
  }
  // Positive minus smaller negative
  {
    let res = &Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &-Integer::from(UnsignedInteger(BoxedUint::one()));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::from(3u8))));
  }
  // Positive minus larger positive
  {
    let res = &Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &Integer::from(UnsignedInteger(BoxedUint::from(3u8)));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::one())));
  }
  // Positive minus larger negative
  {
    let res = &Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &-Integer::from(UnsignedInteger(BoxedUint::from(3u8)));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::from(5u8))));
  }
  // Negative minus smaller positive
  {
    let res = &-Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &Integer::from(UnsignedInteger(BoxedUint::one()));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::from(3u8))));
  }
  // Negative minus smaller negative
  {
    let res = &-Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &-Integer::from(UnsignedInteger(BoxedUint::one()));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::one())));
  }
  // Negative minus larger positive
  {
    let res = &-Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &Integer::from(UnsignedInteger(BoxedUint::from(3u8)));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::from(5u8))));
  }
  // Negative minus larger negative
  {
    let res = &-Integer::from(UnsignedInteger(BoxedUint::from(2u8))) -
      &-Integer::from(UnsignedInteger(BoxedUint::from(3u8)));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.0.ct_eq(&BoxedUint::one())));
  }
}

#[test]
fn test_integer_div() {
  let two = Integer::from(UnsignedInteger(BoxedUint::from(2u8)));
  let neg_two = -two.clone();
  let three = UnsignedInteger(BoxedUint::from(3u8));

  {
    let (res, rem) = &two / &three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value.0, BoxedUint::zero());
    assert_eq!(rem.0, two.value.0);
  }
  {
    let (res, rem) = &-Integer::from(UnsignedInteger(BoxedUint::from(6u8))) / &three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value.0, BoxedUint::from(2u8));
    assert_eq!(rem.0, BoxedUint::zero());
  }
  {
    let (res, rem) = &neg_two / &three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value.0, BoxedUint::one());
    assert_eq!(rem.0, BoxedUint::one());
  }

  let three = Integer::from(three);
  {
    let (res, rem) = &two / &three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value.0, BoxedUint::zero());
    assert_eq!(rem.0, two.value.0);
  }
  {
    let (res, rem) = &neg_two / &three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value.0, BoxedUint::one());
    assert_eq!(rem.0, BoxedUint::one());
  }

  let neg_three = -three;
  {
    let (res, rem) = &two / &neg_three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value.0, BoxedUint::zero());
    assert_eq!(rem.0, two.value.0);
  }
  {
    let (res, rem) = &neg_two / &neg_three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value.0, BoxedUint::one());
    assert_eq!(rem.0, BoxedUint::one());
  }
}

#[test]
fn gcd() {
  // Ensure the underlying crypto-bigint handles the case where one is zero correctly
  assert_eq!(BoxedUint::one().gcd(&BoxedUint::zero()), BoxedUint::one());

  {
    let (gcd, u, v) =
      UnsignedInteger(BoxedUint::one()).extended_gcd(&UnsignedInteger(BoxedUint::zero()));
    assert_eq!(gcd.0, BoxedUint::one());
    assert_eq!(u.0, BoxedUint::one());
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value.0, BoxedUint::zero());
  }

  {
    let (gcd, u, v) =
      UnsignedInteger(BoxedUint::from(2u8)).extended_gcd(&UnsignedInteger(BoxedUint::from(3u8)));
    assert_eq!(gcd.0, BoxedUint::one());
    assert_eq!(u.0, BoxedUint::from(2u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value.0, BoxedUint::one());
  }

  {
    let (gcd, u, v) =
      UnsignedInteger(BoxedUint::from(4u8)).extended_gcd(&UnsignedInteger(BoxedUint::from(8u8)));
    assert_eq!(gcd.0, BoxedUint::from(4u8));
    assert_eq!(u.0, BoxedUint::one());
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value.0, BoxedUint::zero());
  }

  {
    let (gcd, u, v) =
      UnsignedInteger(BoxedUint::from(4u8)).extended_gcd(&UnsignedInteger(BoxedUint::from(10u8)));
    assert_eq!(gcd.0, BoxedUint::from(2u8));
    assert_eq!(u.0, BoxedUint::from(3u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value.0, BoxedUint::one());
  }

  {
    let (gcd, u, v) =
      UnsignedInteger(BoxedUint::from(2u8)).extended_gcd(&UnsignedInteger(BoxedUint::from(2u8)));
    assert_eq!(gcd.0, BoxedUint::from(2u8));
    assert_eq!(u.0, BoxedUint::one());
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value.0, BoxedUint::zero());
  }
}
