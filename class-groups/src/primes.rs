use core::num::NonZero;

use rand::CryptoRng;

use crypto_bigint::{Unsigned, UnsignedWithMontyForm, RandomMod};

/// Get the candidates for the next prime greater than or equal to the seed.
///
/// This function runs in variable time.
///
/// This returns an iterator of candidates.
fn next_prime_candidates<U: Unsigned>(seed: U) -> impl Iterator<Item = U> {
  let max_bit_length = NonZero::new(seed.bits_precision()).unwrap();
  match crypto_primes::hazmat::SmallFactorsSieve::new(seed, max_bit_length, false) {
    Ok(iter) => iter,
    // We explicitly set `max_bit_length = bits_precision`
    Err(crypto_primes::Error::BitLengthTooLarge { .. }) => {
      unreachable!("`max_bit_length = bits_precision`")
    }
    // Inapplicable to this context
    Err(crypto_primes::Error::BitLengthTooSmall { .. }) => unreachable!(),
  }
}

#[derive(Debug)]
pub(super) enum Error {
  NoMillerRabin,
  Capacity,
}

/// Get the next prime greater than or equal to the seed.
///
/// This function runs in variable time.
///
/// The returned value is composite with probability `2^{-bits_of_security}`, per FIPS-186.5, for
/// parameterization of the Miller-Rabin test, unconditionally followed by a Lucas test.
pub(super) fn next_prime<U: UnsignedWithMontyForm + RandomMod>(
  mut rng: impl CryptoRng,
  seed: U,
  bits_of_security: u32,
) -> Result<U, Error> {
  let candidates = next_prime_candidates(seed);
  for candidate in candidates {
    let options =
      crypto_primes::fips::FipsOptions::with_error_bound(candidate.bits(), bits_of_security)
        .ok_or(Error::NoMillerRabin)?
        .with_lucas_test();
    if crypto_primes::fips::is_prime(&mut rng, crypto_primes::Flavor::Any, &candidate, options) {
      return Ok(candidate);
    }
  }
  Err(Error::Capacity)
}
