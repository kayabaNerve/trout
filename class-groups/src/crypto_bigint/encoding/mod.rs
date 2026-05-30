//! Compressed and uncompressed encoding of primitive reduced positive definite binary quadratic
//! forms of negative discriminants (even or odd).
//!
//! Each module contains a documented, exact technical specification as to allow portable
//! interoperability with any other implementation which also implements this specification.
//!
//! All algorithms are presented in a pseudo-code which should be clear to any developer but is not
//! guaranteed to coincide with any specific language or standard. When decoding, we generally use
//! `bytestream.next_byte()` to signify reading the next byte from some (error-free, non-empty,
//! ideal) stream of bytes. This is done to denote how the encodings (and associated decode
//! methods) _do not_ require any encapsulating and are self-contained. They additionally do not
//! explicitly require the ability to look ahead or any external buffers.
//!
//! Our encoding method is _canonical_, only yielding a single encoding for any binary quadratic
//! form. When decoding, we require encodings be canonical. While the simplest check would be to
//! decode, reduce, and re-encode, before checking the equality of the resulting bytes with the
//! input bytes, we provide more cost-effective methods which perform the canonicity checks during
//! the decoding process itself. While this requirement does increase the cost of decoding, we do
//! not find it a considerable portion of a larger context's runtime, but do find malleability too
//! often a footgun to be worth the performance benefits.
//!
//! The following function is used to validate decoded binary quadratic forms as primitive and
//! reduced. It yields `(a, b_positive, b_abs, c)` for valid forms.
//!
//! We assume the existence of a `gcd` function, which for `gcd(x, y)` returns the greatest common
//! divisor of `x, y`.
//!
//! `//` is used to represent floor division.
//!
//! ```py
//! fn validate_binary_quadratic_form(a, b_positive, b_abs, discriminant) {
//!   c = ((b_abs * b_abs) - discriminant) // (4 * a)
//!
//!   # Assert the form is of this discriminant
//!   assert ((b_abs * b_abs) - (4 * a * c)) == discriminant
//!
//!   # Assert the form is reduced
//!   assert b_abs <= a
//!   assert a <= c
//!   # Assert _neither_ `|b| == a, a == c` _or_ that `b_positive == true`
//!   # (as required for a reduced form, when such a equality exists)
//!   assert (!((b_abs == a) || (a == c))) || b_positive
//!   # Assert the form is primitive
//!   assert gcd(a, b_abs, c) == 1
//!
//!   return (a, b_positive, b_abs, c)
//! }
//! ```

use crypto_bigint::{
  Choice, CtOption, CtEq, CtGt, NonZero, ConcatenatingMul, ConcatenatingSquare, Gcd, BoxedUint,
};

/// An error encountered while decoding.
#[derive(Clone, Copy, Debug)]
pub enum Error {
  /// The input stream unexpectedly ended.
  UnexpectedEof,
  /// The value overflowed the intended buffer.
  Overflow,
  /// The value was not canonically encoded.
  NonCanonical,
  /// The value was incorrect.
  Incorrect,
}

/// Validate a positive definite binary quadratic form (of negative discriminant) as primitive and
/// reduced.
///
/// This function runs in constant time.
fn validate_binary_quadratic_form(
  a: NonZero<BoxedUint>,
  (b_positive, b_abs): (Choice, BoxedUint),
  discriminant_abs: &BoxedUint,
) -> CtOption<(NonZero<BoxedUint>, (Choice, BoxedUint), BoxedUint)> {
  let (c, zero) = {
    // This is correct as the discriminant is bound to be negative
    let four_ac = b_abs.concatenating_square().concatenating_add(discriminant_abs);
    let four_a = NonZero::new(a.as_ref().concatenating_mul(BoxedUint::from(4u8)))
      .expect("4 * non-zero value is non-zero");
    four_ac.div_rem(&four_a)
  };

  // Check `b <= a <= c`
  let reduced_absolute_values = (!b_abs.ct_gt(a.as_ref())) & (!a.as_ref().ct_gt(&c));
  // Check the sign of `b` is positive if `a == b` or `a == c`
  let reduced_sign = {
    let has_equality = b_abs.ct_eq(a.as_ref()) | a.as_ref().ct_eq(&c);
    (!has_equality) | b_positive
  };
  // Check it's primitive
  let primitive = a.as_ref().gcd(&b_abs).gcd(&c).is_one();

  CtOption::new(
    (a, (b_positive, b_abs), c),
    zero.is_zero() & reduced_absolute_values & reduced_sign & primitive,
  )
}

mod uncompressed;
pub(crate) use uncompressed::*;

#[cfg(feature = "alloc")]
mod compressed;
#[cfg(feature = "alloc")]
pub(crate) use compressed::*;
