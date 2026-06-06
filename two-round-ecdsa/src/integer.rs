use core::ops::{Add, AddAssign, Mul};

use zeroize::{Zeroize, Zeroizing};
use rand::CryptoRng;

use crypto_bigint::{Resize as _, ConcatenatingMul as _, NonZero, BoxedUint};

/// A constant-time variable-size (dynamically-allocated) unsigned integer.
// This wraps BoxedUint with a type which re-allocates as necessary to ensure it never wraps.
#[derive(Clone, Zeroize)]
pub struct UnsignedInteger(pub(crate) BoxedUint);

impl UnsignedInteger {
  #[must_use]
  pub(crate) fn to_be_bytes(&self) -> Box<[u8]> {
    self.0.to_be_bytes()
  }

  #[must_use]
  pub(crate) fn from_be_slice(slice: &[u8]) -> Self {
    Self(BoxedUint::from_be_slice(slice, u32::try_from(slice.len() * 8).unwrap()).unwrap())
  }

  #[must_use]
  pub(crate) fn random(bits: u32, rng: &mut impl CryptoRng) -> Self {
    let mut bytes = Zeroizing::new(vec![0; bits.div_ceil(8).try_into().unwrap()]);
    rng.fill_bytes(&mut bytes);
    // If we created 8 bits when we were only supposed to create 5 bits...
    if (bits % 8) != 0 {
      // Clear the top bits which shouldn't have been generated
      bytes[0] &= (1 << (bits % 8)) - 1;
    }
    Self(BoxedUint::from_be_slice(&bytes, bits).unwrap())
  }

  #[must_use]
  pub(crate) fn div_rem(&self, denominator: &NonZero<BoxedUint>) -> (Zeroizing<Box<[u8]>>, Self) {
    let denominator_bits = denominator.bits_precision();
    let denominator = denominator.resize(self.0.bits_precision());
    let (d, e) = self.0.div_rem(&denominator);
    let d = Zeroizing::new(d);
    let d = Zeroizing::new(d.to_be_bytes());
    let e = e.resize(denominator_bits);
    (d, Self(e))
  }
}

impl Add for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn add(self, other: Self) -> UnsignedInteger {
    UnsignedInteger(other.0.concatenating_add(&self.0))
  }
}

impl AddAssign for UnsignedInteger {
  fn add_assign(&mut self, other: Self) {
    *self = Self(other.0.concatenating_add(&self.0));
  }
}

impl Mul for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn mul(self, other: Self) -> UnsignedInteger {
    UnsignedInteger(self.0.concatenating_mul(&other.0))
  }
}
