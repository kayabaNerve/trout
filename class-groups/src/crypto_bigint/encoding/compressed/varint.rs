//! Simple and efficient encoding of variably-sized integers
//!
//! This encoding is little-endian, appending the seven _least_-significant bits to a byte vector,
//! until the remaining bits are zero. The eight bit is reserved to mark whether or not the
//! encoding continues.
//!
//! ```py
//! VARINT_VALUE_MASK = (1 << 7) - 1
//! fn encode_varint(value) {
//!   if value == 0 {
//!     return [0]
//!   }
//!
//!   result = []
//!   while value != 0 {
//!     next_byte = value & VARINT_VALUE_MASK
//!     value >>= 7
//!     next_byte |= (value != 0) << 7
//!     result.push(next_byte)
//!   }
//!   return result
//! }
//!
//! fn decode_varint(bytestream) {
//!   result = 0
//!   i = 0
//!   while true {
//!     next_byte = bytestream.next_byte()
//!     result |= (next_byte & VARINT_VALUE_MASK) << i
//!     if (next_byte >> 7) == 0 {
//!       # Check this was canonical, without unnecessary extra bytes
//!       assert (i == 0) || (next_byte != 0)
//!       return result
//!     }
//!     i += 7
//!   }
//! }
//! ```
//!
//! Implementations MUST ensure that `(next_byte & mask) << i` DOES NOT shift any set bits past
//! the boundary of the container. Implementations SHOULD terminate early if `i` exceeds the
//! bit-length of the container (as either a bit will overflow the container, or the final byte
//! will be zero and therefore the number is non-canonically encoded, either case being invalid).

use alloc::{vec::Vec, vec};

#[cfg(feature = "std")]
use std::io;

use super::Error;

const VARINT_VALUE_MASK: u8 = (1 << 7) - 1;

/// This function runs in time variable to the input.
pub(super) fn encode_varint(mut value: usize) -> Vec<u8> {
  if value == 0 {
    return vec![0];
  }

  let mut result = vec![];
  while value != 0 {
    let mut next_byte = u8::try_from(value & usize::from(VARINT_VALUE_MASK)).unwrap();
    value >>= 7;
    next_byte |= u8::from(value != 0) << 7;
    result.push(next_byte);
  }

  result
}

/// This function runs in time variable to the input.
pub(super) fn decode_varint(mut reader: impl io::Read) -> Result<usize, Error> {
  let mut result = 0;
  let mut i = 0;
  while i < usize::BITS {
    let mut next_byte = [0xff];
    reader.read_exact(&mut next_byte).map_err(|_| Error::UnexpectedEof)?;
    let next_byte = next_byte[0];

    let to_shift = next_byte & VARINT_VALUE_MASK;
    {
      let bits_remaining = usize::BITS - i;
      if let Some(expected_not_set_bits) = u8::BITS.checked_sub(bits_remaining) {
        if to_shift.leading_zeros() < expected_not_set_bits {
          Err(Error::Overflow)?;
        }
      }
    }

    result |= usize::from(to_shift) << i;

    if (next_byte >> 7) == 0 {
      if (next_byte == 0) && (i != 0) {
        Err(Error::NonCanonical)?;
      }
      return Ok(result);
    }

    i += 7;
  }
  Err(Error::Overflow)
}

#[test]
fn varint() {
  use rand::Rng as _;
  let mut rng = rand::rand_core::UnwrapErr(rand::rngs::SysRng);

  let test = |value| {
    let encoding = encode_varint(value);
    {
      let mut encoding = encoding.as_slice();
      assert_eq!(decode_varint(&mut encoding).unwrap(), value);
      assert!(encoding.is_empty());
    }
    encoding
  };

  assert_eq!(test(0), vec![0]);
  assert_eq!(test(1), vec![1]);
  assert_eq!(test(usize::from(u8::MAX >> 1)), vec![u8::MAX >> 1]);
  assert_eq!(test(usize::from((u8::MAX >> 1) + 1)), vec![(1 << 7), 1]);

  for _ in 0 .. 256 {
    #[expect(clippy::as_conversions, clippy::cast_possible_truncation)]
    test(rng.next_u64() as usize);
  }

  // TODO: Test error cases
}
