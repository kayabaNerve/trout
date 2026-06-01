//! Compressed and uncompressed encoding of primitive reduced positive definite binary quadratic
//! forms of negative discriminants (even or odd). While this is of greater scope than this library
//! (which restricts itself to odd discriminants), it ensures the wire format allows the library to
//! expand to include also implementing binary quadratic forms of even discriminants (without
//! requiring a distinct encoding specification for those, when the time comes).
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

use crypto_bigint::{Choice, CtOption, CtEq, CtLt, CtAssign, Zero, One, NonZero, Limb};

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

/// The required view over a collection of limbs to validate a binary quadratic form.
pub(super) trait Limbs:
  From<u8> + CtAssign + Zero + One + super::composition::Limbs
{
  /// Divide a wide value by a thin value, yielding the quotient and remainder.
  fn wide_div_rem_thin(wide: Self::Wide, thin: &NonZero<Self>) -> (Self::Wide, Self);
  /// Return if the values are coprime.
  fn coprime(a: Self, b_abs: Self, c: Self::Wide) -> Choice;
}

/// Validate a positive definite binary quadratic form (of negative discriminant) as primitive and
/// reduced.
///
/// This function runs in constant time.
#[expect(clippy::type_complexity)]
pub(super) fn validate_binary_quadratic_form<U: Limbs>(
  a: NonZero<U>,
  (b_positive, b_abs): (Choice, U),
  discriminant_abs: &U::Wide,
) -> CtOption<(NonZero<U>, (Choice, U), U::Wide)> {
  let (c, c_is_correct) = {
    let mut b_square = b_abs.clone().square();

    // This is correct as the discriminant is bound to be negative
    let mut carry = Limb::ZERO;
    for (b_square, discriminant_abs) in <_ as AsMut<[Limb]>>::as_mut(&mut b_square)
      .iter_mut()
      .zip(discriminant_abs.as_ref().iter().chain(core::iter::repeat(&Limb::ZERO)))
    {
      let new_limb;
      (new_limb, carry) = b_square.carrying_add(*discriminant_abs, carry);
      *b_square = new_limb;
    }

    let mut four_ac = b_square;

    {
      let four_ac = <_ as AsMut<[Limb]>>::as_mut(&mut four_ac);
      for i in (0 .. four_ac.len()).rev() {
        let new_limb = (four_ac[i] >> 2) | (carry << (Limb::BITS - 2));
        carry = four_ac[i] & Limb::from(0b11u8);
        four_ac[i] = new_limb;
      }
    }
    let ac = four_ac;

    let (c, rem) = U::wide_div_rem_thin(ac, &a);

    (c, carry.is_zero() & rem.is_zero())
  };

  let reduced_absolute_values;
  let reduced_sign;
  {
    let a = crypto_bigint::UintRef::new(a.as_ref().as_ref());
    let b_abs = crypto_bigint::UintRef::new(b_abs.as_ref());
    let c = crypto_bigint::UintRef::new(c.as_ref());

    // Check `b <= a <= c`
    reduced_absolute_values = (b_abs.ct_lt(a) | b_abs.ct_eq(a)) & (a.ct_lt(c) | a.ct_eq(c));
    // Check the sign of `b` is positive if `a == b` or `a == c`
    reduced_sign = {
      let has_equality = b_abs.ct_eq(a) | a.ct_eq(c);
      (!has_equality) | b_positive
    };
  }
  // Check it's primitive
  let primitive = U::coprime(a.as_ref().clone(), b_abs.clone(), c.clone());

  CtOption::new(
    (a, (b_positive, b_abs), c),
    c_is_correct & reduced_absolute_values & reduced_sign & primitive,
  )
}

mod uncompressed;

#[cfg(feature = "alloc")]
mod compressed;
#[cfg(feature = "alloc")]
pub(crate) use compressed::*;
