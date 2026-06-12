#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![expect(clippy::as_conversions)]

use core::{ops::Neg, fmt};

use crypto_bigint::{
  Choice, CtOption, CtEq as _, NonZero, ConcatenatingSquare as _, Gcd as _, Encoding as _,
  BoxedUint,
};
use class_groups::*;

unsafe extern "C" {
  unsafe fn rust_bicycl_identity_bicycl_qfi(
    discriminant_abs_be_bytes: *const u8,
    discriminant_abs_len: u32,
  ) -> *mut core::ffi::c_void;

  unsafe fn rust_bicycl_new_bicycl_qfi(
    a_be_bytes: *const u8,
    a_len: u32,
    b_be_bytes: *const u8,
    b_len: u32,
    b_is_negative: bool,
    c_be_bytes: *const u8,
    c_len: u32,
  ) -> *mut core::ffi::c_void;

  unsafe fn rust_bicycl_new_bicycl_qfi_discriminant(
    a_be_bytes: *const u8,
    a_len: u32,
    b_be_bytes: *const u8,
    b_len: u32,
    b_is_negative: bool,
    discriminant_be_bytes: *const u8,
    discriminant_len: u32,
  ) -> *mut core::ffi::c_void;

  unsafe fn rust_bicycl_qfi_a(qfi: *mut core::ffi::c_void, len: *mut u32) -> *mut u8;

  unsafe fn rust_bicycl_qfi_b(
    qfi: *mut core::ffi::c_void,
    len: *mut u32,
    is_negative: *mut bool,
  ) -> *mut u8;

  unsafe fn rust_bicycl_qfi_c(qfi: *mut core::ffi::c_void, len: *mut u32) -> *mut u8;

  unsafe fn rust_bicycl_qfi_discriminant_abs(qfi: *mut core::ffi::c_void, len: *mut u32)
  -> *mut u8;

  unsafe fn rust_bicycl_qfi_delete(qfi: *mut core::ffi::c_void);

  unsafe fn rust_bicycl_free(buf: *mut core::ffi::c_void);

  unsafe fn rust_bicycl_qfi_clone(qfi: *mut core::ffi::c_void) -> *mut core::ffi::c_void;

  unsafe fn rust_bicycl_qfi_neg(qfi: *mut core::ffi::c_void);

  unsafe fn rust_bicycl_qfi_double(qfi: *mut core::ffi::c_void) -> *mut core::ffi::c_void;

  unsafe fn rust_bicycl_qfi_add(
    a: *mut core::ffi::c_void,
    b: *mut core::ffi::c_void,
  ) -> *mut core::ffi::c_void;

  unsafe fn rust_bicycl_qfi_sub(
    a: *mut core::ffi::c_void,
    b: *mut core::ffi::c_void,
  ) -> *mut core::ffi::c_void;
}

/// A binary quadratic form deferring to BICYCL for composition.
///
/// This is implemented entirely in variable time.
#[derive(Eq)]
pub struct BicyclElement(usize);

impl fmt::Debug for BicyclElement {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("BicyclElement").finish_non_exhaustive()
  }
}

impl Clone for BicyclElement {
  fn clone(&self) -> Self {
    Self(unsafe { rust_bicycl_qfi_clone(self.0 as *mut core::ffi::c_void) } as usize)
  }
}

impl Drop for BicyclElement {
  fn drop(&mut self) {
    unsafe { rust_bicycl_qfi_delete(self.0 as *mut core::ffi::c_void) }
  }
}

impl PartialEq for BicyclElement {
  fn eq(&self, other: &Self) -> bool {
    self.clone().uncompressed_encode().as_ref() == other.clone().uncompressed_encode().as_ref()
  }
}

impl Neg for BicyclElement {
  type Output = Self;
  fn neg(self) -> Self {
    unsafe {
      rust_bicycl_qfi_neg(self.0 as *mut core::ffi::c_void);
    }
    self
  }
}

unsafe impl Coefficients for BicyclElement {
  fn a_b_c_discriminant(
    self,
  ) -> (impl AsRef<[u8]>, (Choice, impl AsRef<[u8]>), impl AsRef<[u8]>, impl AsRef<[u8]>) {
    let a = {
      let mut len = 0u32;
      let mut res;
      unsafe {
        let bytes = rust_bicycl_qfi_a(self.0 as *mut core::ffi::c_void, &raw mut len);
        res = core::slice::from_raw_parts(bytes, len.try_into().unwrap()).to_vec();
        rust_bicycl_free(bytes.cast::<core::ffi::c_void>());
      }
      let () = res.reverse();
      res
    };

    let b = {
      let mut len = 0u32;
      let mut is_negative = false;
      let mut res;
      unsafe {
        let bytes =
          rust_bicycl_qfi_b(self.0 as *mut core::ffi::c_void, &raw mut len, &raw mut is_negative);
        res = core::slice::from_raw_parts(bytes, len.try_into().unwrap()).to_vec();
        rust_bicycl_free(bytes.cast::<core::ffi::c_void>());
      }
      let () = res.reverse();
      (!Choice::from(u8::from(is_negative)), res)
    };

    let c = {
      let mut len = 0u32;
      let mut res;
      unsafe {
        let bytes = rust_bicycl_qfi_c(self.0 as *mut core::ffi::c_void, &raw mut len);
        res = core::slice::from_raw_parts(bytes, len.try_into().unwrap()).to_vec();
        rust_bicycl_free(bytes.cast::<core::ffi::c_void>());
      }
      let () = res.reverse();
      res
    };

    let discriminant = {
      let mut len = 0u32;
      let mut res;
      unsafe {
        let bytes =
          rust_bicycl_qfi_discriminant_abs(self.0 as *mut core::ffi::c_void, &raw mut len);
        res = core::slice::from_raw_parts(bytes, len.try_into().unwrap()).to_vec();
        rust_bicycl_free(bytes.cast::<core::ffi::c_void>());
      }
      let () = res.reverse();
      res
    };

    (a, b, c, discriminant)
  }
}

impl Element for BicyclElement {
  fn identity(discriminant_abs: impl AsRef<[u8]>) -> Self {
    let mut discriminant_abs = discriminant_abs.as_ref().to_vec();
    let () = discriminant_abs.reverse();
    let discriminant_abs = discriminant_abs.as_slice();
    BicyclElement(unsafe {
      rust_bicycl_identity_bicycl_qfi(
        discriminant_abs.as_ptr(),
        discriminant_abs.len().try_into().unwrap(),
      ) as usize
    })
  }

  fn is_identity(&self) -> Choice {
    let (_a, _b, _c, discriminant) = self.clone().a_b_c_discriminant();
    Choice::from(u8::from(
      self.clone().uncompressed_encode().as_ref() ==
        Self::identity(discriminant).uncompressed_encode().as_ref(),
    ))
  }

  fn double(self) -> Self {
    unsafe { Self(rust_bicycl_qfi_double(self.0 as *mut core::ffi::c_void) as usize) }
  }
  fn add(self, other: Self) -> Self {
    unsafe {
      Self(rust_bicycl_qfi_add(self.0 as *mut core::ffi::c_void, other.0 as *mut core::ffi::c_void)
        as usize)
    }
  }
  fn sub(self, other: Self) -> Self {
    unsafe {
      Self(rust_bicycl_qfi_sub(self.0 as *mut core::ffi::c_void, other.0 as *mut core::ffi::c_void)
        as usize)
    }
  }

  unsafe fn from_coefficients(
    a: impl AsRef<[u8]>,
    (b_positive, b_abs): (Choice, impl AsRef<[u8]>),
    c: impl AsRef<[u8]>,
    _discriminant_abs: impl AsRef<[u8]>,
  ) -> Self {
    let mut a = a.as_ref().to_vec();
    let () = a.reverse();
    let mut b_abs = b_abs.as_ref().to_vec();
    let () = b_abs.reverse();
    let mut c = c.as_ref().to_vec();
    let () = c.reverse();
    BicyclElement(unsafe {
      rust_bicycl_new_bicycl_qfi(
        a.as_ptr(),
        a.len().try_into().unwrap(),
        b_abs.as_ptr(),
        b_abs.len().try_into().unwrap(),
        !bool::from(b_positive),
        c.as_ptr(),
        c.len().try_into().unwrap(),
      ) as usize
    })
  }

  fn uncompressed_encode(self) -> impl AsRef<[u8]> {
    let (a, (b_positive, b_abs), _c, discriminant_abs) = self.a_b_c_discriminant();
    let mut a = a.as_ref().to_vec();
    let mut b_abs = b_abs.as_ref().to_vec();
    let mut discriminant_abs = discriminant_abs.as_ref().to_vec();

    while discriminant_abs.last() == Some(&0) {
      discriminant_abs.pop();
    }
    let floor_log_2_discriminant_abs_plus_one = (8 * (discriminant_abs.len() - 1)) +
      usize::try_from(8 - discriminant_abs.last().unwrap().leading_zeros()).unwrap();
    let floor_log_2_discriminant_abs = floor_log_2_discriminant_abs_plus_one - 1;
    let bits_per_element = (floor_log_2_discriminant_abs / 2) + 1;
    let bytes_per_element = bits_per_element.div_ceil(8);

    a.truncate(bytes_per_element);
    while a.len() < bytes_per_element {
      a.push(0);
    }

    b_abs.truncate(bytes_per_element);
    while b_abs.len() < bytes_per_element {
      b_abs.push(0);
    }
    let mut b = b_abs;
    b[0] ^= u8::from(!b_positive);

    let mut result = a;
    result.extend(b);
    result
  }

  fn uncompressed_decode(
    buf: impl AsRef<[u8]>,
    discriminant_abs: impl AsRef<[u8]>,
  ) -> CtOption<Self> {
    let mut discriminant_abs = discriminant_abs.as_ref().to_vec();

    while discriminant_abs.last() == Some(&0) {
      discriminant_abs.pop();
    }
    if discriminant_abs.is_empty() {
      return CtOption::new(Self(0), Choice::FALSE);
    }
    if (discriminant_abs[0] & 1) != 1 {
      return CtOption::new(Self(0), Choice::FALSE);
    }
    let floor_log_2_discriminant_abs_plus_one = (8 * (discriminant_abs.len() - 1)) +
      usize::try_from(8 - discriminant_abs.last().unwrap().leading_zeros()).unwrap();
    let floor_log_2_discriminant_abs = floor_log_2_discriminant_abs_plus_one - 1;
    let bits_per_element = (floor_log_2_discriminant_abs / 2) + 1;
    let bytes_per_element = bits_per_element.div_ceil(8);

    let buf = buf.as_ref();
    if buf.len() != (2 * bytes_per_element) {
      return CtOption::new(Self(0), Choice::FALSE);
    }

    let mut a = buf[.. bytes_per_element].to_vec();
    let () = a.reverse();
    let mut b_abs = buf[bytes_per_element ..].to_vec();
    let b_positive = (b_abs[0] & 1).ct_eq(&1);
    if bool::from(!b_positive) {
      b_abs[0] ^= 1;
    }
    let () = b_abs.reverse();

    let () = discriminant_abs.reverse();

    {
      let a = BoxedUint::from_be_bytes(a.clone().into());
      let b_abs = BoxedUint::from_be_bytes(b_abs.clone().into());
      let discriminant_abs = BoxedUint::from_be_bytes(discriminant_abs.clone().into());
      let four_ac = b_abs.concatenating_square().concatenating_add(discriminant_abs);
      let (four_c, rem) = four_ac.div_rem(&{
        let Some(a) = Option::<NonZero<BoxedUint>>::from(NonZero::new(a.clone())) else {
          return CtOption::new(Self(0), Choice::FALSE);
        };
        a
      });
      if bool::from(!rem.is_zero()) {
        return CtOption::new(Self(0), Choice::FALSE);
      }
      let (c, rem) = four_c.div_rem(&NonZero::new(BoxedUint::from(4u8)).unwrap());
      if bool::from(!rem.is_zero()) {
        return CtOption::new(Self(0), Choice::FALSE);
      }
      if b_abs > a {
        return CtOption::new(Self(0), Choice::FALSE);
      }
      if a > c {
        return CtOption::new(Self(0), Choice::FALSE);
      }
      if !((!((b_abs == a) || (a == c))) || bool::from(b_positive)) {
        return CtOption::new(Self(0), Choice::FALSE);
      }
      if bool::from(!a.gcd(&b_abs).gcd(&c).is_one()) {
        return CtOption::new(Self(0), Choice::FALSE);
      }
    }

    CtOption::new(
      BicyclElement(unsafe {
        rust_bicycl_new_bicycl_qfi_discriminant(
          a.as_ptr(),
          a.len().try_into().unwrap(),
          b_abs.as_ptr(),
          b_abs.len().try_into().unwrap(),
          !bool::from(b_positive),
          discriminant_abs.as_ptr(),
          discriminant_abs.len().try_into().unwrap(),
        ) as usize
      }),
      Choice::TRUE,
    )
  }
}

#[test]
fn bicycl() {
  let mut rng = rand::rand_core::UnwrapErr(rand::rngs::SysRng);

  let prime =
    crypto_primes::random_prime::<BoxedUint, _>(&mut rng, crypto_primes::Flavor::Any, 256);
  let cg = Cl15p::<BoxedUint, BoxedUint, BoxedUint, BoxedUint>::sample(
    rng,
    128,
    2046,
    crypto_bigint::Odd::new(prime).unwrap(),
  )
  .unwrap();

  let crypto_bigint_g = {
    use crypto_bigint::RandomMod as _;
    let discriminant_abs = cg.absolute_value();
    let discriminant_abs = discriminant_abs.as_ref();
    let seed = BoxedUint::random_mod_vartime(
      &mut rng,
      &NonZero::new(
        BoxedUint::from_le_slice_vartime(discriminant_abs).wrapping_shr_vartime(2).floor_sqrt(),
      )
      .unwrap(),
    );
    CryptoBigintElement::<BoxedUint>::next_prime_ideal_squared(rng, seed, discriminant_abs, 128)
  };
  let bicycl_g = <BicyclElement as class_groups::Element>::from(crypto_bigint_g.clone());

  assert_eq!(
    crypto_bigint_g,
    <CryptoBigintElement::<BoxedUint> as class_groups::Element>::from(bicycl_g.clone())
  );
  assert_eq!(
    crypto_bigint_g,
    <CryptoBigintElement::<BoxedUint> as class_groups::Element>::from(
      BicyclElement::uncompressed_decode(
        crypto_bigint_g.clone().uncompressed_encode(),
        cg.absolute_value()
      )
      .unwrap()
    )
  );
  assert_eq!(
    crypto_bigint_g.clone().double(),
    <CryptoBigintElement::<BoxedUint> as class_groups::Element>::from(bicycl_g.clone().double())
  );
  assert!(bool::from(bicycl_g.clone().sub(bicycl_g.clone()).is_identity()));

  {
    let mut bicycl_g = bicycl_g.clone();
    let start = std::time::Instant::now();
    for _ in 0 .. 100_000 {
      bicycl_g = bicycl_g.clone().add(bicycl_g);
    }
    println!("100,000 `BicyclElement` NUCOMPs: {}ms", start.elapsed().as_millis());
  }

  {
    let mut crypto_bigint_g =
      <class_groups::CryptoBigintElement<crypto_bigint::U1280> as class_groups::Element>::from(
        crypto_bigint_g,
      );
    let start = std::time::Instant::now();
    for _ in 0 .. 100_000 {
      crypto_bigint_g = crypto_bigint_g.clone().add(crypto_bigint_g);
    }
    println!("100,000 `CryptoBigintElement::<U1280>` NUCOMPs: {}ms", start.elapsed().as_millis());
  }
}
