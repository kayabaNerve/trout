use core::marker::PhantomData;
use std::io;

use crypto_bigint::{Encoding as _, BoxedUint};
use class_groups::{ElementExt, NegativeDiscriminant as _, Cl15p};

use crate::UnsignedInteger;

mod round_one;
pub use round_one::*;

mod round_two;
pub use round_two::*;

/*
  Reader/Writer which transcripts what they read/write. The Reader avoids the read, decompress,
  compress, hash flow solely read, hash, decompress. Since compressions can be expensive, this
  is greatly appreciated, while the pattern also ensures our transcript is complete.
*/

/// A reader which transcripts as it reads.
pub struct DigestReader<R: io::Read>(pub(crate) blake3::Hasher, pub(crate) R);
impl<R: io::Read> io::Read for DigestReader<R> {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let read_bytes = self.1.read(buf)?;
    if read_bytes > buf.len() {
      Err(io::Error::other("more bytes read than size of buffer"))?;
    }
    self.0.update(&buf[.. read_bytes]);
    Ok(read_bytes)
  }
}

/// A writer which transcripts as it writes.
pub struct DigestWriter<W: io::Write>(pub(crate) blake3::Hasher, pub(crate) W);
impl<W: io::Write> io::Write for DigestWriter<W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    self.0.update(buf);
    self.1.write(buf)
  }
  fn flush(&mut self) -> io::Result<()> {
    self.1.flush()
  }
}

/// A source of prime numbers.
pub trait Primes {
  /// Derive a prime number from the XOF.
  ///
  /// The prime number MUST be sampled from the primes `2 < prime < 2**lambda`. Different
  /// satisfiers of this trait MAY yield distinct results, making the choice for `Primes` part of
  /// the protocol.
  ///
  /// This function is assumed to execute in variable time. This function has undefined behavior
  /// when `lambda <= 1`.
  fn prime(lambda: u32, xof: blake3::OutputReader) -> UnsignedInteger;
}

mod crypto_primes {
  use super::*;

  // Wrap the XOF into an RNG to satisfy crypto_primes's requirement for an RNG
  struct Blake3Rng(blake3::OutputReader);
  impl rand::TryRng for Blake3Rng {
    type Error = rand::rand_core::Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
      let mut bytes = [0; 4];
      self.0.fill(&mut bytes);
      Ok(u32::from_le_bytes(bytes))
    }
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
      let mut bytes = [0; 8];
      self.0.fill(&mut bytes);
      Ok(u64::from_le_bytes(bytes))
    }
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
      self.0.fill(dst);
      Ok(())
    }
  }
  impl rand::TryCryptoRng for Blake3Rng {}

  /// A source of primes premised on crypto-primes.
  ///
  /// Panics at runtime if asked for a prime larger than its generic.
  ///
  /// This is here for evaluation purposes. It is not posited to be uniform and accordingly isn't
  /// posited to be secure. Results may differ across patch versions of crypto-primes.
  // https://github.com/entropyxyz/crypto-primes/issues/23
  // https://github.com/entropyxyz/crypto-primes/issues/25
  pub struct CryptoPrimesStack<
    U: crypto_bigint::UnsignedWithMontyForm
      + crypto_bigint::RandomBits
      + crypto_bigint::RandomMod
      + crypto_bigint::Encoding,
  >(PhantomData<U>);
  impl<
    U: crypto_bigint::UnsignedWithMontyForm
      + crypto_bigint::RandomBits
      + crypto_bigint::RandomMod
      + crypto_bigint::Encoding,
  > Primes for CryptoPrimesStack<U>
  {
    fn prime(lambda: u32, xof: blake3::OutputReader) -> UnsignedInteger {
      let mut rng = Blake3Rng(xof);
      loop {
        let candidate =
          ::crypto_primes::random_prime::<U, _>(&mut rng, ::crypto_primes::Flavor::Any, lambda);
        if bool::from(crypto_bigint::Integer::is_even(&candidate)) {
          continue;
        }
        break UnsignedInteger::from_be_slice(candidate.to_be_bytes().as_ref());
      }
    }
  }

  /// CryptoPrimesStack, guaranteed to not panic when used with this library's Ccykc* proofs.
  pub type CryptoPrimesStackCcykc = CryptoPrimesStack<crypto_bigint::U128>;

  /// A source of primes premised on crypto-primes.
  ///
  /// This is here for evaluation purposes. It is not posited to be uniform and accordingly isn't
  /// posited to be secure. Results may differ across patch versions of crypto-primes.
  // https://github.com/entropyxyz/crypto-primes/issues/23
  // https://github.com/entropyxyz/crypto-primes/issues/25
  pub struct CryptoPrimesHeap;
  impl Primes for CryptoPrimesHeap {
    fn prime(lambda: u32, xof: blake3::OutputReader) -> UnsignedInteger {
      let mut rng = Blake3Rng(xof);
      loop {
        let candidate = ::crypto_primes::random_prime::<crypto_bigint::BoxedUint, _>(
          &mut rng,
          ::crypto_primes::Flavor::Any,
          lambda,
        );
        if bool::from(crypto_bigint::Integer::is_even(&candidate)) {
          continue;
        }
        break UnsignedInteger::from_be_slice(candidate.to_be_bytes().as_ref());
      }
    }
  }
}
pub use crypto_primes::*;

pub(crate) mod ccykc {
  use std::io::{self, Read, Write};

  use super::*;

  pub(crate) const LAMBDA: u32 = 128;
  const EPSILON_D: u32 = 128;
  const B_CONST: u32 = EPSILON_D + LAMBDA + 2;
  pub(crate) fn B<F: group::ff::PrimeField>(
    class_group: &Cl15p<BoxedUint, BoxedUint, BoxedUint, BoxedUint>,
  ) -> u32 {
    /*
      The `1 +` is because the paper says to sample from `[-B, B]`. We sample from the equally
      large range `[0, 2B] which should be as uniform since this is in-effect modulo the unknown
      order bound (or a composite number where that's one of the factors), without needing to deal
      with signed integers.

      We technically don't sample from `[0, 2B]` yet `[0, 2**log_2(2B)]`. The verifier doesn't
      require a certian bound, the prover doesn't lose completeness with such a bound, and this is
      should still be as uniform since we our log_2 is rounding up. It's arguably slightly more
      inefficient, due to the extra bit, yet avoids calculation of `B`.
    */
    1 + (B_CONST + F::NUM_BITS + class_group.upper_bound_on_order())
  }

  pub(crate) fn write_e<W: Write>(
    transcript: &mut DigestWriter<W>,
    modulus: &crypto_bigint::NonZero<crypto_bigint::BoxedUint>,
    e: &UnsignedInteger,
  ) -> io::Result<()> {
    let e_bytes = e.to_be_bytes();
    // We can fix the encoded size to the size of the modulus, known to the prover and verifier
    let e_expected_bytes = usize::try_from(modulus.bits().div_ceil(8)).unwrap();
    // If our response is longer (due to `div_rem` not sufficiently shortening), only write the
    // expected bytes. The cut-off bytes should all be zero as they're above the modulus.
    let e_bytes = if e_expected_bytes <= e_bytes.len() {
      &e_bytes[(e_bytes.len() - e_expected_bytes) ..]
    } else {
      // If our response is shorter, prefix the BE encoding with the proper amount of zero bytes
      transcript.write_all(&vec![0; e_expected_bytes - e_bytes.len()])?;
      &e_bytes
    };
    transcript.write_all(e_bytes)
  }

  pub(crate) fn read_e<R: Read>(
    transcript: &mut DigestReader<R>,
    modulus: &BoxedUint,
  ) -> io::Result<BoxedUint> {
    let mut e = vec![0; modulus.bits().div_ceil(8).try_into().unwrap()];
    transcript.read_exact(&mut e)?;
    let e_int = BoxedUint::from_be_bytes(e.into());
    if e_int > *modulus {
      Err(io::Error::other("unreduced e"))?;
    }
    Ok(e_int)
  }
}
