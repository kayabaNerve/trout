//! Encapsulated encoding of unsigned big integers
//!
//! ```py
//! fn encode_bigint(bigint) {
//!   bytes = bigint.to_le_bytes()
//!   # Trim any trailing zero bytes
//!   while bytes.len() != 0 {
//!     if bytes[bytes.len() - 1] == 0 {
//!       bytes.pop()
//!     }
//!   }
//!
//!   result = encode_varint(bytes.len())
//!   result.extend(bytes)
//!   return result
//! }
//!
//! fn decode_bigint(bytestream) {
//!   len = decode_varint(bytestream)
//!   result = []
//!   while len != 0 {
//!     result.push(bytestream.next_byte())
//!     len -= 1
//!   }
//!
//!   # Check this was canonical, without unnecessary extra bytes
//!   if result.len() != 0 {
//!     assert result[result.len() - 1] != 0
//!   }
//!
//!   return BigInt::from_le_bytes(result)
//! }
//! ```
//!
//! Implementations SHOULD bound the size of big integers, as context allows, to prevent any
//! denial-of-service attacks. Implementations MUST ensure any bounds exceed any possible valid
//! value's length.
//!
//! This encoding method was chosen as in practice, one expects to encode big integers of up to
//! approximately 64-256 bytes. At this scale, the VarInt encoding method does not remain
//! efficient, justifying the usage of either a fixed-length or length-prefixed encoding instead.
//! As numbers are sufficiently often of low norm, length-prefixed encodings are preferable.

use alloc::{vec::Vec, vec};

#[cfg(feature = "std")]
use std::io;

use crypto_bigint::BoxedUint;

use super::{Error, varint::*};

/// This function runs in time variable to the input.
pub(super) fn encode_bigint(bigint: &BoxedUint) -> Vec<u8> {
  let bytes = bigint.to_le_bytes();
  let mut bytes = bytes.as_ref();
  while bytes.last() == Some(&0) {
    bytes = &bytes[.. bytes.len() - 1];
  }

  let mut result = encode_varint(bytes.len());
  result.extend(bytes);
  result
}

/// This function runs in time variable to the input.
#[cfg(feature = "std")]
pub(super) fn decode_bigint(mut reader: impl io::Read, bit_bound: u32) -> Result<BoxedUint, Error> {
  let result = BoxedUint::from_le_slice(
    ({
      let len = decode_varint(&mut reader)?;
      let mut buf = vec![0xff; len];
      reader.read_exact(&mut buf).map_err(|_| Error::UnexpectedEof)?;

      if buf.last() == Some(&0) {
        Err(Error::NonCanonical)?;
      }

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
  use crypto_bigint::RandomBits;

  let mut rng = rand::rand_core::UnwrapErr(rand::rngs::SysRng);

  let test = |value| {
    let encoding = encode_bigint(&value);
    {
      let mut encoding = encoding.as_slice();
      assert_eq!(decode_bigint(&mut encoding, value.bits_precision()).unwrap(), value);
      assert!(encoding.is_empty());
    }
    encoding
  };

  assert_eq!(test(BoxedUint::zero()), vec![0]);
  assert_eq!(test(BoxedUint::one()), vec![1, 1]);

  for i in 0 .. 256 {
    test(BoxedUint::random_bits(&mut rng, 8 * i));
  }

  // TODO: Test error cases
}
