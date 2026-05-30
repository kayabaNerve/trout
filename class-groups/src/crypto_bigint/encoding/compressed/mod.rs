//! Compression of binary quadratic forms
//!
//! This implements compression of primitive reduced positive definite binary quadratic forms of
//! negative discriminants (even or odd) such that they can represented in approximately
//! `2 + 1.5 (floor(log_2(sqrt(|discriminant|))) + 1)` bits instead of the naïvely required
//! `1 + 2 (floor(log_2(sqrt(|discriminant|))) + 1)` (the absolute value of the `a`, `b`
//! coefficients and the sign of the `b` coefficient).
//!
//! The methodology is as posited in
//! [Trustless unknown-order groups](https://eprint.iacr.org/2020/196) by Samuel Dobson,
//! Steven Galbraith, and Benjamin Smith. They do describe a rather complete description of
//! compression, and the result, which we appreciate but continue the specification of (and
//! somewhat differ from).
//!
//! Notably, instead of encoding the `b` coefficient as a pair of congruences, we encode the `b`
//! coefficient as the result of a Euclidean division. This avoids having to find a solution for
//! `f`, which lacked bounds (and presumably only had a statistical bound regarding the
//! distribution of prime factors).
//!
//! We bound to primitive forms as we do not practically want to work with imprimitive forms and
//! MUST eventially validate all forms to be primitive (upon decode being the logical place to do
//! so, ensuring imprimitive forms never even enter our context). We bound to reduced forms to
//! ensure a canonical representation. We bound to positive definite forms (of negative
//! discriminant) to ensure the `a` coefficient is positive and non-zero, as required for the
//! compression algorithm (to avoid it as an exceptional case).
//!
//! The pseudocode denotes what we would discuss as `z'` as `z_apo`, instead of the more
//! traditional `z_prime` (for arbitrary "z"). This is to avoid confusion on if this variable is
//! notably considered (co)prime.
//!
//! We assume the existence of a `gcd` function, which for `gcd(x, y)` returns the greatest common
//! divisor of `x, y`. We also assume the existence of an `xgcd` function, which for `xgcd(x, y)`,
//! returns `(u, v, d)` where `u * x + v * y = d` and `d = gcd(x, y)`.
//!
//! `//` is used to represent floor division.
//!
//! ```py
//! fn encode_compressed_binary_quadratic_form(a, b_positive, b_abs) {
//!   (t_positive, t_abs) = t(a, b_abs)
//!   g = gcd(a, t_abs)
//!   a_apo = a / g
//!   t_apo_abs = t_abs / g
//!   b_0 = b_abs // a_apo
//!
//!   result = encode_bigint(a_apo)
//!   result.extend(encode_bigint(g))
//!   result.push((t_positive << 1) | b_positive)
//!   result.extend(encode_bigint(t_apo_abs))
//!   result.extend(encode_bigint(b_0))
//!   return result
//! }
//!
//! # Note `discriminant` is a _signed_ big integer, bound to be negative
//! fn decode_compressed_binary_quadratic_form(bytestream, discriminant) {
//!   # This is bounded to be less than the square root
//!   # of the absolute value of the discriminant
//!   a_apo = decode_bigint(bytestream)
//!
//!   # This is bounded to be less than the fourth root
//!   # of the absolute value of the discriminant
//!   g = decode_bigint(bytestream)
//!
//!   a = a_apo * g
//!   # For a negative discriminant, `a != 0`
//!   assert a != 0
//!
//!   sign_bits = bytestream.next_byte()
//!   # Ensure `sign_bits` was canonically encoded
//!   assert (sign_bits >> 2) == 0
//!   b_positive = sign_bits & 1
//!   t_positive = sign_bits >> 1
//!
//!   # This is bounded to be less than the fourth root
//!   # of the absolute value of the discriminant
//!   t_apo_abs = decode_bigint(bytestream)
//!
//!   t_abs = t_apo_abs * g
//!   # We ignore the sign of `t` here as `-1 * -1 = 1`
//!   x = (t_abs * t_abs * discriminant) % a
//!
//!   s = floor_sqrt(x)
//!   assert (s * s) == x
//!
//!   s_apo = s // g
//!   assert (s_apo * g) == s
//!   # `u t_apo_abs + v a_apo = d` where `d = gcd(a, b)`
//!   (u, _v, one) = xgcd(t_apo_abs, a_apo)
//!   # This asserts the modular inverse exists and that `g = gcd(t, a)`
//!   assert one == 1
//!   b_apo = (s_apo * u) % a_apo
//!   # If `t` was negative, negate `b_apo % a_apo`
//!   if (b_apo != 0) && (!t_positive) {
//!     b_apo = a_apo - b_apo
//!   }
//!
//!   # This is bounded to be less than `g`, which is less than the fourth root
//!   # of the absolute value of the discriminant
//!   b_0 = decode_bigint(bytestream)
//!   assert b_0 <= g
//!   b_abs = (b_0 * a_apo) + b_apo
//!
//!   # Assert `t` was canonically chosen
//!   assert (t_positive, t_abs) == t(a, b_abs)
//!
//!   return validate_binary_quadratic_form(a, b_positive, b_abs, discriminant)
//! }
//!
//! The total bounds on the bits read is actually slighty more than the bit-length of the absolute
//! value of the discriminant. This is explained by how these bounds _overlap_. `a_apo, g`
//! _together_ are of bit-length approximate to the square root of the absolute value of the
//! discriminant. Similarly, `b_0` has bit-length approximate to `g`, but `t_apo_abs, g`
//! _together_ are of bit-length approximate to the fourth root of the absolute value of the
//! discriminant (and therefore `t_apo_abs, b_0` are _together_ of bit-length approximate to the
//! fourth root of the absolute value of the discriminant). This results in the total amount of
//! bits being approximate to just `2 + 1.5 (floor(log_2(sqrt(|discriminant|))) + 1)`, as desired.

use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::io;

use crypto_bigint::{
  Choice, CtEq, CtAssign, NonZero, ConcatenatingMul, ConcatenatingSquare, Gcd, Resize, BoxedUint,
};

use super::Error;

mod varint;

mod bigint;
use bigint::{encode_bigint, decode_bigint};

mod partial_xgcd;
use partial_xgcd::t;

/// This function runs in time variable to the input.
pub(crate) fn encode_compressed_binary_quadratic_form(
  a: NonZero<BoxedUint>,
  b_positive: Choice,
  b_abs: BoxedUint,
) -> Vec<u8> {
  let (t_positive, t_abs) = t(a.clone(), b_abs.clone());
  let g = a.gcd_vartime(&t_abs);
  let a = a.get();
  let a_apo = &a / &g;
  let a_apo = NonZero::new(a_apo.clone()).expect("`a != 0` so `(a / gcd(a, t)) != 0`");
  let t_apo_abs = t_abs.get() / &g;
  let b_0 = b_abs / &a_apo;

  let mut result = encode_bigint(a_apo.as_ref());
  result.extend(&encode_bigint(g.as_ref()));
  result.push((u8::from(t_positive) << 1) | u8::from(b_positive));
  result.extend(&encode_bigint(&t_apo_abs));
  result.extend(&encode_bigint(&b_0));
  result
}

/// This function runs in time variable to the input.
#[cfg(feature = "std")]
#[expect(clippy::type_complexity)]
pub(crate) fn decode_compressed_binary_quadratic_form(
  mut reader: impl io::Read,
  discriminant_abs: &BoxedUint,
) -> Result<(NonZero<BoxedUint>, (Choice, BoxedUint), BoxedUint), Error> {
  let bits_per_element = discriminant_abs.bits().div_ceil(2);
  debug_assert!(discriminant_abs.floor_sqrt_vartime().bits() <= bits_per_element);

  let a_apo = decode_bigint(&mut reader, bits_per_element)?;
  let a_apo = NonZero::new(a_apo).ok_or(Error::Incorrect)?;
  let g = decode_bigint(&mut reader, bits_per_element.div_ceil(2))?;
  let g = Option::<NonZero<_>>::from(NonZero::new(g)).ok_or(Error::Incorrect)?;
  let a = a_apo.concatenating_mul(g.as_ref());
  let a = NonZero::new(a).expect("the product of two non-zero values is itself non-zero");

  let (b_positive, b_abs) = {
    let mut sign_bits = [0xff];
    reader.read_exact(&mut sign_bits).map_err(|_| Error::UnexpectedEof)?;
    let sign_bits = sign_bits[0];
    if (sign_bits >> 2) != 0 {
      Err(Error::NonCanonical)?;
    }
    let b_positive = (sign_bits & 1).ct_eq(&1);
    let t_positive = (sign_bits >> 1).ct_eq(&1);

    let t_apo_abs = decode_bigint(&mut reader, bits_per_element.div_ceil(2))?;
    if bool::from(t_apo_abs.is_zero()) {
      Err(Error::Incorrect)?;
    }
    let t_abs = t_apo_abs.concatenating_mul(g.as_ref());

    let b_abs = {
      let s_apo = {
        let s = {
          let x = t_abs.square_mod(&a).mul_mod(discriminant_abs, &a).neg_mod(&a);

          let s = x.floor_sqrt_vartime();
          if s.concatenating_square() != x {
            Err(Error::Incorrect)?;
          }
          s
        };

        let (s_apo, zero) = s.div_rem(&g);
        if bool::from(!zero.is_zero()) {
          Err(Error::Incorrect)?;
        }
        s_apo
      };

      if bool::from(!t_apo_abs.gcd_vartime(&a_apo).is_one()) {
        Err(Error::Incorrect)?;
      }
      let u = t_apo_abs
        .resize(bits_per_element)
        .invert_mod(&a_apo)
        .expect("non-zero and coprime but no modular inverse?");
      let mut b_apo = s_apo.mul_mod(&u, &a_apo);
      b_apo.ct_assign(&b_apo.neg_mod(&a_apo), !t_positive);

      let b_0 = decode_bigint(&mut reader, g.bits_vartime())?;
      if b_0 > *g {
        Err(Error::Incorrect)?;
      }

      b_0.concatenating_mul(a_apo.as_ref()).concatenating_add(&b_apo)
    };
    if b_abs > (*a.as_ref()) {
      Err(Error::Incorrect)?;
    }

    {
      let (t_positive_recalculated, t_abs_recalculated) = t(a.clone(), b_abs.clone());
      if (bool::from(t_positive), t_abs) !=
        (bool::from(t_positive_recalculated), t_abs_recalculated.get())
      {
        Err(Error::NonCanonical)?;
      }
    }

    (b_positive, b_abs)
  };

  Option::from(super::validate_binary_quadratic_form(a, (b_positive, b_abs), discriminant_abs))
    .ok_or(Error::Incorrect)
}
