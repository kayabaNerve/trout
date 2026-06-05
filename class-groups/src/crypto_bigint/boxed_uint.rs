use crypto_bigint::{
  CtEq, CtAssign, Resize, Zero, One, ConcatenatingSquare, ConcatenatingMul, Gcd, Choice, NonZero,
  BoxedUint,
};

impl super::c::Limbs for BoxedUint {
  #[inline(always)]
  fn widening_square(&self) -> (Self, Self) {
    let size = self.bits_precision();
    let square = self.concatenating_square().clone();
    let hi = (&square >> size).resize_unchecked(size);
    let lo = square.resize_unchecked(size);
    (lo, hi)
  }
  #[inline(always)]
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self {
    let denom_bits = denom.bits_precision();
    let num =
      num.1.resize_unchecked(2 * denom_bits).overflowing_shl_vartime(denom_bits).unwrap() | num.0;
    // The caller is bound to not pass `0` as the denominator
    let (quotient, remainder) = num.div_rem(&denom.to_nz().unwrap());
    debug_assert!(bool::from(remainder.is_zero()));
    quotient.resize_unchecked(denom_bits)
  }
  #[inline(always)]
  fn rem(num: Self, denom: &Self) -> Self {
    num.div_rem(&NonZero::new(denom.clone()).unwrap()).1
  }
}

impl super::reduction::Limbs for BoxedUint {
  #[inline(always)]
  fn like_zero(&self) -> Self {
    Zero::zero_like(self)
  }
}

impl super::composition::Limbs for BoxedUint {
  type Wide = BoxedUint;
  #[expect(private_interfaces)]
  fn xgcd(self, other: Self) -> super::composition::Xgcd<Self> {
    // The documentation on the `trait` allows us to make these bounds
    debug_assert!(bool::from(!self.is_zero()));
    debug_assert!(bool::from(!other.is_zero()));

    // `BoxedUint` has a `gcd` method but not an `xgcd` method, so we calculate `u, v` ourselves
    // We know the `gcd` is non-zero as the inputs are non-zero
    let gcd = NonZero::new(self.gcd(&other)).unwrap();

    // Calculate `u` as the modular inverse of `self % other`
    let u = {
      let self_div_gcd = &self / &gcd;
      let other_div_gcd = &other / &gcd;
      /*
        This has a modular inverse as these are coprime, which will be true UNLESS `self` is itself
        a factor (or multiple) of `other`. In this case, the coefficients are `0, 1` or `1, 0`.
      */
      let u = self_div_gcd.invert_mod(&NonZero::new(other_div_gcd).unwrap());
      let u_if_divisible =
        BoxedUint::from(u8::from(self_div_gcd.is_one())).resize_unchecked(other.bits_precision());
      u.unwrap_or(u_if_divisible)
    };

    /*
      Calculate `v` as `(ua - d) / b`.

      We explicitly use a `wrapping_sub` as `ua = 0` occurs when `b | a`. This causes an invalid
      value to be assigned to `v`, but we then correct it to `1` if so.
    */
    /*
      TODO: The composition algorithm doesn't need this coefficient for one of its two calls to
      `xgcd`. If we split the `xgcd` function into one which returns the `u` coefficient and one
      which returns the `u` and `v` coefficients, we can optimize this out.
    */
    let v =
      ((u.concatenating_mul(&self)).wrapping_sub(&*gcd)) / NonZero::new(other.clone()).unwrap();
    let mut v = v.resize_unchecked(self.bits_precision());
    // If `u = 0` because `b` is a factor of `a`, correct the `v` coefficient to `1`
    v.ct_assign(&BoxedUint::one_like(&v), u.is_zero());

    /*
      Return `u` as the positive coefficient, `v` as the negative coefficient, as it's our choice
      when we know the inputs are non-zero EXCEPT when one is a factor of the other. In this case,
      both are positive as one coefficient will be zero.
    */
    let v_sign = u.is_zero();

    #[cfg(debug_assertions)]
    {
      use crypto_bigint::CtSelect;
      let eq1 = u.concatenating_mul(&self);
      let eq2 = v.concatenating_mul(&other);
      let lhs = <_>::ct_select(
        &(eq1.wrapping_sub(&eq2).concatenating_add(BoxedUint::zero())),
        &eq1.concatenating_add(&eq2),
        v_sign,
      );
      debug_assert!(bool::from(lhs.ct_eq(&*gcd)));
    }

    super::composition::Xgcd { d: gcd.get(), u: (Choice::TRUE, u), v: (v_sign, v) }
  }
  #[inline(always)]
  fn div(self, denom: &Self) -> Self {
    self.div_rem(&NonZero::new(denom.clone()).unwrap()).0
  }
  #[inline(always)]
  fn mul_mod(&self, other: &Self, modulus: &Self) -> Self {
    let product = self.mul_mod(other, &NonZero::new(modulus.clone()).unwrap());
    product.resize_unchecked(modulus.bits_precision())
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

impl super::composition::WideLimbs<BoxedUint> for BoxedUint {
  #[inline(always)]
  fn rem(self, denom: &BoxedUint) -> Self {
    let remainder = self.div_rem(&NonZero::new(denom.clone()).unwrap()).1;
    remainder.resize_unchecked(denom.bits_precision())
  }
}

impl super::encoding::Limbs for BoxedUint {
  fn wide_div_rem_thin(wide: Self::Wide, thin: &NonZero<Self>) -> (Self::Wide, Self) {
    wide.div_rem(thin)
  }

  fn coprime(a: Self, b_abs: Self, c: Self::Wide) -> Choice {
    a.gcd(&b_abs).gcd(&c).is_one()
  }
}

impl super::element::Limbs for BoxedUint {
  type Bytes = Box<[u8]>;

  #[inline(always)]
  fn max_bits() -> Option<u32> {
    None
  }

  #[inline(always)]
  fn truncate(wide: Self::Wide, bits: u32) -> Self {
    wide.resize_unchecked(bits)
  }
  #[inline(always)]
  fn widen(thin: Self, wide_bits: u32) -> Self::Wide {
    thin.resize_unchecked(wide_bits)
  }

  #[inline(always)]
  fn to_le_bytes(self) -> Self::Bytes {
    BoxedUint::to_le_bytes(&self)
  }
  #[inline(always)]
  fn wide_to_le_bytes(wide: Self::Wide) -> impl AsRef<[u8]> {
    BoxedUint::to_le_bytes(&wide)
  }

  #[inline(always)]
  fn from_le_slice(mut bytes: &[u8], max_bits: u32) -> Self {
    while ((8 * u32::try_from(bytes.len().saturating_sub(1)).unwrap()) >= max_bits) &&
      bytes.last().map(|byte| bool::from(byte.ct_eq(&0))).unwrap_or(false)
    {
      bytes = &bytes[.. (bytes.len() - 1)];
    }
    Self::from_le_slice(bytes, max_bits).unwrap()
  }
  #[inline(always)]
  fn wide_from_le_slice(mut bytes: &[u8], max_bits: u32) -> Self::Wide {
    while ((8 * u32::try_from(bytes.len().saturating_sub(1)).unwrap()) >= max_bits) &&
      bytes.last().map(|byte| bool::from(byte.ct_eq(&0))).unwrap_or(false)
    {
      bytes = &bytes[.. (bytes.len() - 1)];
    }
    Self::from_le_slice(bytes, max_bits).unwrap()
  }

  fn stitch(first: Self::Bytes, second: Self::Bytes, bytes_per_element: usize) -> impl AsRef<[u8]> {
    [&first[.. bytes_per_element], &second[.. bytes_per_element]].concat()
  }
}
