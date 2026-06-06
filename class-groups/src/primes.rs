use core::num::NonZero;

use rand::CryptoRng;
use crypto_bigint::BoxedUint;

/// Get the candidates for the next prime greater than or equal to the seed.
///
/// The seed is specified by its big-endian encoding.
///
/// This returns the bit-length of the seed and an iterator of candidates.
///
/// This may panic if an obscenely large seed is specified.
fn next_prime_candidates(seed: BoxedUint) -> (u32, impl Iterator<Item = BoxedUint>) {
  let bit_length = seed.bits();
  let max_bit_length = NonZero::new(seed.bits_precision()).unwrap();
  match crypto_primes::hazmat::SmallFactorsSieve::new(seed, max_bit_length, false) {
    Ok(iter) => (bit_length, iter),
    // We explicitly set `max_bit_length = bits_precision`
    Err(crypto_primes::Error::BitLengthTooLarge { .. }) => {
      unreachable!("`max_bit_length = bits_precision`")
    }
    // Inapplicable to this context
    Err(crypto_primes::Error::BitLengthTooSmall { .. }) => unreachable!(),
  }
}

/// Get the next prime greater than or equal to the seed.
///
/// The seed is specified by its big-endian encoding.
///
/// The returned value is composite with probability `2^{-bits_of_security}`, per FIPS-186.5, for
/// parameterization of the Miller-Rabin test, followed by a Lucas test.
///
/// This may panic if an obscenely large seed is specified or if the bits of security don't
/// correspond to an amount of iterations for the Miller-Rabin test (with bit-length equal to the
/// bit-length of the number represented by the seed). This may panic if no prime could be found.
pub(super) fn next_prime(
  rng: &mut impl CryptoRng,
  seed: impl AsRef<[u8]>,
  bits_of_security: u32,
) -> BoxedUint {
  let seed = BoxedUint::from_be_slice_vartime(seed.as_ref());
  let (bit_length, candidates) = next_prime_candidates(seed);
  let options = crypto_primes::fips::FipsOptions::with_error_bound(bit_length, bits_of_security)
    .expect("bits of security lacked corresponding Miller-Rabin profile")
    .with_lucas_test();
  for candidate in candidates {
    if crypto_primes::fips::is_prime(rng, crypto_primes::Flavor::Any, &candidate, options) {
      return candidate;
    }
  }

  panic!("exhausted all candidates within at least a further 8 bits")
}
