#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![expect(non_snake_case)]
#![no_std]

extern crate alloc;
use alloc::vec;
extern crate std;
use std::io;

use zeroize::Zeroize;
use rand::CryptoRng;

use group::{
  ff::{Field as _, PrimeField as _},
  Group,
  prime::PrimeGroup,
};

use crypto_bigint::{
  CtSelect, Zero, Limb, NegMod, ConcatenatingMul, ConcatenatingSquare, InvertMod, BitOps, Encoding,
  RandomBits, Resize as _, BoxedUint,
};

use cshake::digest::{CustomizedInit, Update, ExtendableOutput, XofReader};

mod non_interactive_setup;
pub use non_interactive_setup::NonInteractiveSetup;

mod setup;
pub use setup::{InteractiveSetup, InteractiveSetupWithDerivations};
pub(crate) use setup::SigningKey;

mod batch_verifier;
use batch_verifier::BatchVerifier;

mod ciphertext;
pub(crate) use ciphertext::Ciphertext;
mod commitment;
pub(crate) use commitment::Commitment;
mod dual_scaled_decryption;
pub(crate) use dual_scaled_decryption::DualScaledDecryption;

mod preprocess;
pub use preprocess::{Preprocess, PreprocessOpening, Aggregating, AggregatePreprocess};
mod sign;
pub use sign::{Sign, Completing, CompletingWithoutIdentifiableAborts};

mod ciphersuites;
pub use ciphersuites::*;

/// A wrapper for `R: io::Read` which copies read bytes.
struct CopyRead<R: io::Read, W: io::Write> {
  read: R,
  copy_to: W,
}
impl<R: io::Read, W: io::Write> io::Read for CopyRead<R, W> {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let len = self.read.read(buf)?;
    self.copy_to.write_all(&buf[.. len])?;
    Ok(len)
  }
}

trait CShake: Clone + CustomizedInit + Update + ExtendableOutput {
  /// The bits of security offered by this instance of CShake.
  const BITS_OF_SECURITY: u16;
}
impl CShake for cshake::CShake128 {
  const BITS_OF_SECURITY: u16 = 128;
}
impl CShake for cshake::CShake256 {
  const BITS_OF_SECURITY: u16 = 256;
}

/// A group wrapped with the necessary helpers for Trout++.
pub trait WrappedGroup {
  /// The group this wraps.
  type G: PrimeGroup<Scalar: Zeroize + CtSelect>;

  /// The integer type which can store the prime order of this group.
  type Up: Clone
    + AsRef<[Limb]>
    + AsMut<[Limb]>
    + PartialOrd
    + Zeroize
    + CtSelect
    + Zero
    + NegMod<Output = Self::Up>
    + for<'a> ConcatenatingMul<&'a Self::Up, Output: Encoding>
    + ConcatenatingSquare<Output: Encoding>
    + InvertMod<Output = Self::Up>
    + BitOps
    + Encoding
    + RandomBits;

  /// The domain-separation tag identifying this ciphersuite.
  ///
  /// This MUST be a recognized label for an elliptic curve ("P-224", "P-256", "P-384", "P-521").
  ///
  /// `Self::BITS_OF_SECURITY`, `Self::generator_e()` MUST be singular and explicitly defined with
  /// regards to the domain separation tag.
  const DST: &[u8];

  /// The bits of security this targets.
  const BITS_OF_SECURITY: u16;

  /// The cSHAKE instance used.
  ///
  /// The bits of security from cSHAKE MUST be the first choice greater than or equal to
  /// `Self::BITS_OF_SECURITY`.
  #[expect(private_bounds)]
  type CShake: CShake;

  /// The generator of this group used for public keys.
  fn generator_e() -> Self::G;

  /// Deserialize a point from a _canonical_ encoding.
  fn point_from_canonical_bytes(transcript: impl io::Read) -> io::Result<Self::G>;

  /// Reduce the `x`-coordinate of a point into a scalar.
  fn x_coordinate(point: &Self::G) -> <Self::G as Group>::Scalar;

  /// Hash the message and reduce it into a scalar.
  fn hash_message(message: impl AsRef<[u8]>) -> <Self::G as Group>::Scalar;

  /// Squeeze a scalar from the sponge.
  fn squeeze_scalar(xof: &mut impl XofReader) -> <Self::G as Group>::Scalar;
}

type Up2<G> = <<G as WrappedGroup>::Up as ConcatenatingSquare>::Output;

// TODO: https://github.com/RustCrypto/crypto-bigint/issues/1275
#[allow(non_snake_case)]
fn Up_zero_with_precision<Up: AsMut<[Limb]> + RandomBits>(bits_precision: u32) -> Up {
  struct Zero;
  impl crypto_bigint::rand_core::TryRng for Zero {
    type Error = crypto_bigint::rand_core::Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
      Ok(0)
    }
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
      Ok(0)
    }
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
      for b in dst {
        *b = 0;
      }
      Ok(())
    }
  }
  let mut result = Up::random_bits_with_precision(&mut Zero, 0, bits_precision);
  for limb in result.as_mut() {
    *limb = Limb::ZERO;
  }
  result
}

/// Return a `Up` with value equal to the integer value of a scalar.
///
/// This assumes the amount of bits required to represent a scalar is less than or equal to the
/// capacity of `Up.`
///
/// This function runs in time only variable to the amount of bits needed to represent a scalar and
/// is independent to the value of the scalar itself.
fn Up_from_scalar<Up: AsMut<[Limb]> + BitOps + RandomBits, G: WrappedGroup>(
  mut scalar: <G::G as Group>::Scalar,
) -> Up {
  let mut result = Up_zero_with_precision::<Up>(<G::G as Group>::Scalar::NUM_BITS);

  for i in 0 .. <G::G as Group>::Scalar::NUM_BITS {
    let b = scalar.is_odd();

    // Write this bit into the `Up`
    result.set_bit(i, b.into());

    // Clear this bit and shift the scalar by one
    scalar -=
      <_>::ct_select(&<G::G as Group>::Scalar::ZERO, &<G::G as Group>::Scalar::ONE, b.into());
    scalar *= <G::G as Group>::Scalar::TWO_INV;
  }

  result
}

/// Return `p: Up` with value the order of the elliptic curve.
///
/// This assumes the order of the elliptic curve is _odd_ (not `2`) and`p` has capacity greater
/// than or equal to the amount of bits in the representation of the order of the elliptic curve.
///
/// This function runs in time only variable to the amount of bits needed to represent a scalar and
/// is independent to the value of the order itself.
fn p_Up<Up: AsMut<[Limb]> + BitOps + RandomBits, G: WrappedGroup>() -> Up {
  let mut p = Up_from_scalar::<Up, G>(-<G::G as Group>::Scalar::ONE);
  assert!(!p.bit_vartime(0), "-1 isn't even so the order of the elliptic curve is not odd");
  p.set_bit_vartime(0, true);
  p
}

/// Sample a challenge.
///
/// The result is of form $(c_\mathsf{prime}, c)$.
///
/// The result is completely deterministic to `xof`, except with statistical negligibility (if the
/// primality tests disagree). The RNG is only used for entropy for said primality tests.
fn challenge<G: WrappedGroup>(
  rng: impl CryptoRng,
  xof: &mut impl XofReader,
) -> (BoxedUint, <G::G as Group>::Scalar) {
  let bytes = (2 * u32::from(G::BITS_OF_SECURITY)).div_ceil(8);
  let bits = 8 * bytes;

  let mut prime =
    vec![0; usize::from(u16::try_from(bytes).expect(r"$\lceil (2 * x) / 8 \rceil \le x$"))];
  xof.read(&mut prime);
  let first_odd_prime = BoxedUint::from(3u8).resize(bits);
  let prime = match class_groups::primes::next_prime(
    rng,
    BoxedUint::from_le_bytes(prime.into()),
    u32::from(G::BITS_OF_SECURITY),
  ) {
    Ok(prime) => {
      if prime.bits() <= bits {
        prime
      } else {
        first_odd_prime
      }
    }
    Err(class_groups::primes::Error::NoMillerRabin) => {
      panic!("invalid ciphersuite definition (no Miller-Rabin parameters)")
    }
    Err(class_groups::primes::Error::Capacity) => first_odd_prime,
  };

  let challenge = G::squeeze_scalar(xof);

  (prime, challenge)
}

/// An ECDSA signature.
pub struct Signature<G: WrappedGroup> {
  /// The `x`-coordinate of the nonce commitment, reduced into the scalar field.
  pub r: <G::G as Group>::Scalar,
  /// The signature.
  pub s: <G::G as Group>::Scalar,
}
