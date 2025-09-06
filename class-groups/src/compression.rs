use core::cmp::Ordering;
use std::io;

use ::malachite::{
  base::num::{arithmetic::traits::*, basic::traits::*},
  *,
};

use crate::malachite::{natural_from_bytes, natural_to_bytes};

/// Calculate the `f` used when compressing/decompressing.
///
/// Assumes `g`, `a_` are non-zero, `a >= a'`.
pub(crate) fn f(a: &Natural, a_: &Natural, g: Natural) -> Natural {
  let mut f = g;
  while {
    let (gcd, _x, _y) = f.clone().extended_gcd(a_);
    let lcm = (&f * a_) / gcd;
    lcm < *a
  } {
    f += Natural::ONE;
  }
  f
}

/// The `PartialXGCD` algorithm used when compressing.
pub(crate) fn partial_xgcd(a: Natural, b: Natural) -> (Natural, Integer) {
  /*
    `s` is checked to be `>=` this value, where `s` is a integer and this sqrt may not be. If
    the sqrt is `1.5`, for `s` to be `>=`, it must be `>= 2` (since it itself is an integer).
    Hence the use of a ceiling sqrt, as a floor sqrt would let an integer smaller than the
    sqrt be `>=`.
  */
  let a_sqrt = a.clone().ceiling_sqrt();
  let (mut s, mut s_, mut t, mut t_, mut u, mut u_) = (
    Integer::from(b.clone()),
    Integer::from(a.clone()),
    Integer::ONE,
    Integer::ZERO,
    Integer::ZERO,
    Integer::ONE,
  );
  while s >= a_sqrt {
    let q = &s_ / &s;
    (s, s_, t, t_, u, u_) = (s_ - (&q * &s), s, t_ - (&q * &t), t, u_ - (&q * &u), u);
  }
  // But `s` won't be negative, only `t` may be
  debug_assert!(s.sign() != Ordering::Less);
  let s = s.unsigned_abs();
  debug_assert!(s < a_sqrt);
  debug_assert_eq!(&s % &a, {
    let product = Integer::from(b.clone()) * &t;
    let candidate = product.unsigned_abs_ref() % &a;
    if product.sign() == Ordering::Less { (&a - candidate) % &a } else { candidate }
  });
  (s, t)
}

/// Reconstruct a value via a pair of congruences.
///
/// The moduli are assumed to be non-zero.
pub(crate) fn crt(a1: Natural, n1: Natural, a2: Natural, n2: Natural) -> io::Result<Natural> {
  let (g, u, v) = (&n1).extended_gcd(&n2);
  if (&a1 % &g) != (&a2 % &g) {
    Err(io::Error::other("CRT has no solution"))?;
  }
  let M = (&n1 / &g) * &n2;
  let x = ((Integer::from(&a1 * &n2) * &v) + (Integer::from(&a2 * &n1) * &u)) / Integer::from(g);

  let x_sign = x.sign();
  let x = x.unsigned_abs() % &M;
  Ok(if x_sign == Ordering::Less { &M - x } else { x })
}

/// Write a value, encoded as a VarInt, LE-chunked with the MSB first within a chunk.
///
/// This takes an initialization value for the first byte, allowing packing the encoding of this
/// VarInt with another value. In that case, `first_byte_bits_available` must be set to the amount
/// of bits still available in the *LSBs* of the first byte.
pub(crate) fn write_varint(
  mut writer: impl io::Write,
  first_byte_init: u8,
  first_byte_bits_available: u8,
  mut value: usize,
) -> io::Result<()> {
  let mut byte_init = first_byte_init;
  // The highest bit is the continuation mask, and this is the amount of bits for the value itself
  let mut bits: u8 = first_byte_bits_available - 1;
  let mut first = true;
  while first || (value != 0) {
    first = false;
    // The next byte is the low bits in the VarInt...
    // This unwrap will never trip as u8 is itself a u8, meaning we only have u8-bits here
    let mut next = u8::try_from(value & usize::from((1u8 << bits) - 1)).unwrap();
    value >>= bits;
    // Plus the initialization
    next |= byte_init;
    // If we have to continue, set the high bit after the mask
    let continuation = value != 0;
    if continuation {
      next |= 1 << bits;
    }
    writer.write_all(&[next])?;

    // Clear the byte init
    byte_init = 0;
    // Use the full byte for all future bytes
    bits = 7;
  }
  Ok(())
}

/// Write a `Natural`.
///
/// This will prefix it with a VarInt-encoded length. For more details on this, and the
/// `first_byte_*` arguments, please see `write_varint`.
pub(crate) fn write_number(
  mut writer: impl io::Write,
  first_byte_init: u8,
  first_byte_bits_available: u8,
  value: &Natural,
) -> io::Result<()> {
  let bytes = natural_to_bytes(value);
  write_varint(&mut writer, first_byte_init, first_byte_bits_available, bytes.len())?;
  writer.write_all(&bytes)
}

/// Read a byte.
pub(crate) fn read_byte(mut reader: impl io::Read) -> io::Result<u8> {
  let mut byte = [0xff];
  reader.read_exact(&mut byte)?;
  Ok(byte[0])
}

/// Read a VarInt-encoded number.
///
/// This is limited to reading 32-bit numbers *after all shifts are applied*. In practice, this
/// may mean even smaller numbers are the limit depending on where chunk boundaries lie.
///
/// The first byte to be read as part of the VarInt is passed in, along with the bits used for the
/// VarInt-encoded number *within this byte*.
pub(crate) fn read_varint(
  mut reader: impl io::Read,
  first_byte: u8,
  first_byte_bits: u8,
) -> io::Result<usize> {
  let mut byte = first_byte;
  // The highest bit is the continuation mask, and this is the amount of bits for the value itself
  let mut bits = first_byte_bits - 1;
  let mut res = 0;
  let mut total_bits = 0;
  // Read bytes until we no longer have a continuation mask
  while (byte & (1 << bits)) != 0 {
    res |= usize::from(byte & ((1 << bits) - 1)) << total_bits;
    total_bits += bits;
    // This means we exit the loop with `total_bits <= 25`, letting us safely accumulate the
    // final (up to) 7 bits
    if total_bits > 25 {
      return Err(io::Error::other("varint overflow"));
    }
    byte = read_byte(&mut reader)?;
    bits = 7;
  }
  // Accumulate the last byte
  let last_byte = usize::from(byte & ((1 << bits) - 1)) << total_bits;
  if (total_bits != 0) && (last_byte == 0) {
    Err(io::Error::other("non-canonical varint"))?;
  }
  res |= last_byte;
  Ok(res)
}

/// Read a `Natural`.
///
/// This does not read any length-prefix, such as the one prefixed when calling `write_number`, and
/// must be passed in the length of the byte-encoding of the number being read.
pub(crate) fn read_number(mut reader: impl io::Read, len: usize) -> io::Result<Natural> {
  let mut num = vec![0xff; len];
  reader.read_exact(&mut num)?;
  if let Some(b) = num.first() &&
    (*b == 0)
  {
    return Err(io::Error::other("non-canonical bignum"));
  }
  Ok(natural_from_bytes(&num))
}

pub(crate) fn read_epsilon_a_g_t_b_0(
  mut reader: impl io::Read,
) -> io::Result<(u8, Natural, Natural, Integer, Natural)> {
  let first_byte = read_byte(&mut reader)?;
  let (epsilon, t_is_negative) = {
    // (epsilon << 1) + t_is_negative
    let sign_bits = first_byte >> 6;
    let t_is_negative = sign_bits & 1;
    let epsilon = sign_bits >> 1;
    (epsilon, t_is_negative)
  };

  let a_len = read_varint(&mut reader, first_byte, 6)?;
  let a_ = read_number(&mut reader, a_len)?;

  let mut read_number = || {
    let first_byte = read_byte(&mut reader)?;
    let len = read_varint(&mut reader, first_byte, 8)?;
    read_number(&mut reader, len)
  };
  let g = read_number()?;
  let t_ = read_number()?;
  let mut t_ = Integer::from(t_);
  if t_is_negative == 1 {
    if t_ == Integer::ZERO {
      Err(io::Error::other("negative zero for t'"))?;
    }
    t_ = -t_;
  }
  let b_0 = read_number()?;

  Ok((epsilon, a_, g, t_, b_0))
}

#[test]
fn varint_encoding() {
  use rand::{Rng, rngs::SysRng};

  // 0 should encode as a single 0 byte
  {
    let mut bytes = vec![];
    write_varint(&mut bytes, 0, 8, 0).unwrap();
    assert_eq!(bytes, vec![0]);
    assert_eq!(read_varint(&mut &bytes[1 ..], bytes[0], 8).unwrap(), 0);
  }

  // Test with a short first byte
  #[allow(clippy::unusual_byte_groupings)]
  {
    let mut bytes = vec![];
    write_varint(&mut bytes, 0b111111 << 2, 2, 1).unwrap();
    assert_eq!(bytes, vec![0b111111_01]);
  }
  #[allow(clippy::unusual_byte_groupings)]
  {
    let mut bytes = vec![];
    write_varint(&mut bytes, 0b111111 << 2, 2, 2).unwrap();
    // (continuation byte, MSB in LE chunk), (no continuation byte, next LE chunk)
    assert_eq!(bytes, vec![0b111111_10, 1]);
  }

  // Test 100 random values
  for _ in 0 .. 100 {
    let value = usize::try_from(rand::rand_core::UnwrapErr(SysRng).next_u64() % (1 << 20)).unwrap();
    let mut bytes = vec![];
    write_varint(&mut bytes, 0, 8, value).unwrap();
    assert_eq!(read_varint(&mut &bytes[1 ..], bytes[0], 8).unwrap(), value);
  }
}

#[test]
fn test_crt() {
  use rand::{Rng, rngs::SysRng};

  let test = |n1, n2| {
    let value = Natural::from(rand::rand_core::UnwrapErr(SysRng).next_u64());
    assert_eq!(
      crt(&value % &n1, n1.clone(), &value % &n2, n2.clone()).unwrap(),
      value % (&n1 * &n2)
    );
  };
  test(Natural::from(1u64), Natural::from(19u64));
  test(Natural::from(7u64), Natural::from(1u64));
  test(Natural::from(7u64), Natural::from(19u64));
}
