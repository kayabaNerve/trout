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
//! We assume the existence of:
//! - A `gcd` function, which for `gcd(x, y)` returns the greatest common divisor of `x, y`
//! - An `xgcd` function, which for `xgcd(x, y)`, returns `(u, v, d)` where `u * x + v * y = d` and
//!   `d = gcd(x, y)`.
//! - A `floor_sqrt` function, which for `floor_sqrt(x)`, returns `y` where $y^2 \le x < (y + 1)^2$
//! - A `floor_log_2` function, which for `floor_log_2(x)`, returns `k` such that
//!   $2^k \le x < 2^{k + 1}$
//!
//! `//` is used to represent floor division.
//!
//! ```py
//! # Note `discriminant` is a _signed_ big integer, bound to be negative
//! fn encode_compressed_binary_quadratic_form(a, b_positive, b_abs, discriminant) {
//!   (t_positive, t_abs) = t(a, b_abs)
//!   g = gcd(a, t_abs)
//!   a_apo = a / g
//!   t_apo_abs = t_abs / g
//!   b_0 = b_abs // a_apo
//!
//!   g_bits = floor_log_2(g) + 1
//!   result = encode_varint(g_bits)
//!   result.extend(encode_bigint(a_apo, (floor_log_2(-discriminant) // 2) + 1 - (g_bits - 1)))
//!   result.extend(encode_bigint(g, g_bits))
//!   result.push((t_positive << 1) | b_positive)
//!   result.extend(encode_bigint(t_apo_abs, (floor_log_2(-discriminant) // 4) + 1 - (g_bits - 1)))
//!   result.extend(encode_bigint(b_0, g_bits))
//!   return result
//! }
//!
//! # Note `discriminant` is a _signed_ big integer, bound to be negative
//! fn decode_compressed_binary_quadratic_form(bytestream, discriminant) {
//!   g_bits = decode_varint(bytestream)
//!   assert g_bits <= (floor_log_2(-discriminant) // 2) + 1
//!   a_apo = decode_bigint(bytestream, (floor_log_2(-discriminant) // 2) + 1 - (g_bits - 1))
//!   g = decode_bigint(bytestream, g_bits)
//!   assert g_bits == (floor_log_2(g) + 1)
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
//!   t_apo_abs = decode_bigint(bytestream, (floor_log_2(-discriminant) // 4) + 1 - (g_bits - 1))
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
//!   b_0 = decode_bigint(bytestream, g_bits)
//!   assert b_0 <= g
//!   b_abs = (b_0 * a_apo) + b_apo
//!
//!   # Assert `b_abs <= a`
//!   # This is a prerequisite for calling `t`, which so bounds its inputs
//!   assert b_abs <= a
//!   # Assert `t` was canonically chosen
//!   assert (t_positive, t_abs) == t(a, b_abs)
//!
//!   return validate_binary_quadratic_form(a, b_positive, b_abs, discriminant)
//! }
//! ```
//!
//! When decoding `a_apo, g`, their bit bounds are such that their product is at most the square
//! root of the discriminant. Note these bit bounds aren't strictly enforced, solely used to
//! determine the lengths of the big integers' encodings, and we ensure they're canonical via
//! validating `g_bits` upon deserialization and ensuring the resulting form is in fact reduced.
//! Similarly, when decoding `t_apo_abs, b_0`, their bit bounds are such that their product is at
//! most the fourth root of the discriminant (if the bit bounds were enforced, where we do validate
//! `b_0 <= g` and then validate `t` was canonically chosen and therefore `t_apo_abs` was correctly
//! encoded). This causes the encoding, ignoring the alignment of the big integers to byte
//! boundaries, to be of length $v + \lfloor log_2(-discriminant)^{3 / 4} \rfloor + 11$ where $v$
//! is the length of the VarInt encoding of $g_bits$ (experimentally, $1$ in the average case).
//! Note most of the $11$ is from using an entire byte to represent the two sign bits, $b_positive$
//! and $t_positive$.

use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::io;

use crypto_bigint::{
  Choice, CtEq, CtAssign, NonZero, ConcatenatingMul, ConcatenatingSquare, Gcd, Resize, BoxedUint,
};

use super::Error;

mod varint;
use varint::{encode_varint, decode_varint};

mod bigint;
use bigint::{encode_bigint, decode_bigint};

mod partial_xgcd;
use partial_xgcd::t;

/// This function runs in time variable to the input.
pub(crate) fn encode_compressed_binary_quadratic_form(
  a: NonZero<BoxedUint>,
  b_positive: Choice,
  b_abs: BoxedUint,
  discriminant_abs: &BoxedUint,
) -> Vec<u8> {
  let (t_positive, t_abs) = t(a.clone(), b_abs.clone());
  let g = a.gcd_vartime(&t_abs);
  let a = a.get();
  let a_apo = &a / &g;
  let a_apo = NonZero::new(a_apo.clone()).expect("`a != 0` so `(a / gcd(a, t)) != 0`");
  let t_apo_abs = t_abs.get() / &g;
  let b_0 = b_abs / &a_apo;

  let g_bits = usize::try_from(g.bits()).unwrap();
  let mut result = encode_varint(g_bits);
  result.extend(&encode_bigint(
    a_apo.as_ref(),
    ((usize::try_from(discriminant_abs.bits()).unwrap() - 1) / 2) + 1 - (g_bits - 1),
  ));
  result.extend(&encode_bigint(g.as_ref(), g_bits));
  result.push((u8::from(t_positive) << 1) | u8::from(b_positive));
  result.extend(&encode_bigint(
    &t_apo_abs,
    ((usize::try_from(discriminant_abs.bits()).unwrap() - 1) / 4) + 1 - (g_bits - 1),
  ));
  result.extend(&encode_bigint(&b_0, g_bits));
  result
}

/// This function runs in time variable to the input.
#[cfg(feature = "std")]
#[expect(clippy::type_complexity)]
pub(crate) fn decode_compressed_binary_quadratic_form(
  mut reader: impl io::Read,
  discriminant_abs: &BoxedUint,
) -> Result<(NonZero<BoxedUint>, (Choice, BoxedUint), BoxedUint), Error> {
  debug_assert!(
    discriminant_abs.floor_sqrt_vartime().bits() <= ((discriminant_abs.bits() - 1) / 2) + 1
  );
  debug_assert!(
    discriminant_abs.floor_sqrt_vartime().floor_sqrt_vartime().bits() <=
      ((discriminant_abs.bits() - 1) / 4) + 1
  );

  let g_bits = u32::try_from(decode_varint(&mut reader)?).map_err(|_| Error::Overflow)?;
  if g_bits > (((discriminant_abs.bits() - 1) / 2) + 1) {
    Err(Error::Incorrect)?;
  }
  let a_apo = decode_bigint(&mut reader, ((discriminant_abs.bits() - 1) / 2) + 1 - (g_bits - 1))?;
  let a_apo = NonZero::new(a_apo).ok_or(Error::Incorrect)?;
  let g = decode_bigint(&mut reader, g_bits)?;
  if g.bits() != g_bits {
    Err(Error::NonCanonical)?;
  }
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

    let t_apo_abs =
      decode_bigint(&mut reader, ((discriminant_abs.bits() - 1) / 4) + 1 - (g_bits - 1))?;
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
        .resize(a_apo.bits_precision())
        .invert_mod(&a_apo)
        .expect("non-zero and coprime but no modular inverse?");
      let mut b_apo = s_apo.mul_mod(&u, &a_apo);
      b_apo.ct_assign(&b_apo.neg_mod(&a_apo), !t_positive);

      let b_0 = decode_bigint(&mut reader, g_bits)?;
      if b_0 > *g {
        Err(Error::Incorrect)?;
      }

      b_0.concatenating_mul(a_apo.as_ref()).concatenating_add(&b_apo)
    };

    {
      if b_abs > (*a.as_ref()) {
        Err(Error::Incorrect)?;
      }
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
