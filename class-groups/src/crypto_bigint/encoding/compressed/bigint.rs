//! Encoding of unsigned big integers of size known ahead of time
//!
//! ```py
//! fn encode_bigint(bigint, bits) {
//!   result = bigint.to_le_bytes()
//!   # Trim any trailing zero bytes
//!   while result.len() != 0 {
//!     if result[result.len() - 1] == 0 {
//!       result.pop()
//!     }
//!   }
//!   # Pad this to the bound, as necessary
//!   while result.len() < ((bits + 7) / 8) {
//!     result.push(0)
//!   }
//!   return result
//! }
//!
//! fn decode_bigint(bytestream, bits) {
//!   result = []
//!   while result.len() != ((bits + 7) / 8) {
//!     result.push(bytestream.next_byte())
//!   }
//!   return BigInt::from_le_bytes(result)
//! }
//! ```
//!
//! This accepts bit bounds for the size of the integers, from which it applies a ceiling division
//! to obtain a byte bound for the length of the encoding, but the bit bound is never strictly
//! enforced. These methods assume the caller will ensure the encoded values were appropriate. The
//! alignment to byte boundaries is to simplify decoding.

use alloc::{vec::Vec, vec};

#[cfg(feature = "std")]
use std::io;

use crypto_bigint::BoxedUint;

use super::Error;

/// This function runs in time variable to the input.
pub(super) fn encode_bigint(bigint: &BoxedUint, bits: usize) -> Vec<u8> {
  let mut result = bigint.to_le_bytes().to_vec();
  while result.last() == Some(&0) {
    result.pop();
  }
  while result.len() < bits.div_ceil(8) {
    result.push(0);
  }
  result
}

/// This function runs in time variable to the input.
#[cfg(feature = "std")]
pub(super) fn decode_bigint(mut reader: impl io::Read, bit_bound: u32) -> Result<BoxedUint, Error> {
  let result = BoxedUint::from_le_slice(
    ({
      let mut buf = vec![0xff; usize::try_from(bit_bound.div_ceil(8)).unwrap()];
      reader.read_exact(&mut buf).map_err(|_| Error::UnexpectedEof)?;
      buf
    })
    .as_slice(),
    bit_bound,
  )
  .map_err(|_| Error::Overflow)?;
  Ok(result)
}

#[test]
fn bigint() {
  use crypto_bigint::{RandomBits as _, Uint};

  let mut rng = rand::rand_core::UnwrapErr(rand::rngs::SysRng);

  let test = |value| {
    let encoding = encode_bigint(&value, usize::try_from(value.bits_precision()).unwrap());
    {
      let mut encoding = encoding.as_slice();
      assert_eq!(decode_bigint(&mut encoding, value.bits_precision()).unwrap(), value);
      assert!(encoding.is_empty());
    }
    encoding
  };

  assert_eq!(test(BoxedUint::zero()), vec![0; Uint::<1>::BYTES]);
  assert_eq!(test(BoxedUint::one()), {
    let mut one = vec![0; Uint::<1>::BYTES];
    one[0] = 1;
    one
  });

  for i in 0 .. 256 {
    test(BoxedUint::random_bits(&mut rng, 8 * i));
  }

  // TODO: Test error cases
}
