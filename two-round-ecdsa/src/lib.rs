#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(non_snake_case, clippy::too_many_arguments, clippy::type_complexity)]

use core::marker::PhantomData;
use std::io;

use subtle::{Choice, ConditionallySelectable};
use zeroize::{Zeroize, Zeroizing};

use group::{ff::PrimeFieldBits, GroupEncoding, prime::PrimeGroup};
use class_groups::Element;

mod integer;
pub use integer::UnsignedInteger;

/// ZK proofs included for the protocols.
pub mod proofs;
pub(crate) use proofs::*;

mod key_gen;
pub use key_gen::*;

mod sign;
pub use sign::*;

pub(crate) struct ToLeBits<F: PrimeFieldBits> {
  underlying: group::ff::FieldBits<F::ReprBits>,
  i: usize,
}
impl<F: PrimeFieldBits> Iterator for ToLeBits<F> {
  type Item = Choice;
  fn next(&mut self) -> Option<Choice> {
    if self.i >= usize::try_from(F::NUM_BITS).unwrap() {
      None?;
    }
    let mut bit_raw = self.underlying.get_mut(self.i).unwrap();
    self.i += 1;

    // The following black_box/Zeroizing are a best-effort, horrific attempt to avoid side-channels
    let bit_bool =
      Zeroizing::new(*core::hint::black_box(core::convert::AsRef::<bool>::as_ref(&bit_raw)));
    // zeroize the underlying bitstore as we iterate so secret material isn't left behind
    core::convert::AsMut::<bool>::as_mut(&mut bit_raw).zeroize();
    let bit_u8 = u8::from(core::hint::black_box(*bit_bool));
    Some(bit_u8.into())
  }
}
/// Alternative to `to_le_bits` which returns `Choice` instead of `bool`
pub(crate) fn const_to_le_bits<F: PrimeFieldBits>(scalar: &F) -> ToLeBits<F> {
  ToLeBits { underlying: scalar.to_le_bits(), i: 0 }
}

pub(crate) fn be_bytes<F: PrimeFieldBits>(scalar: &F) -> Vec<u8> {
  let mut bytes = vec![0; F::NUM_BITS.div_ceil(8).try_into().unwrap()];
  for (i, bit) in const_to_le_bits(scalar).enumerate() {
    // The least-significant bit goes into the last unpopulated byte
    let byte = bytes.len() - ((i / 8) + 1);
    bytes[byte] |= u8::conditional_select(&0, &(1 << (i % 8)), bit);
  }
  bytes
}

/// Parameters for the signing protocol.
pub trait Parameters<CG: Element>: Sized {
  /// The elliptic curve.
  type E: PrimeGroup<Scalar = Self::F>;
  /// The scalar field of the elliptic curve.
  type F: Zeroize + PrimeFieldBits + group::ff::FromUniformBytes<64>;

  /// The round one proofs.
  type RoundOneProofs: RoundOneProofs<CG, Self>;
  /// The round two proofs.
  type RoundTwoProofs: RoundTwoProofs<CG, Self>;

  /// Read a `E` while enforcing a canonical encoding.
  ///
  /// The provided implementation assumes encodings are always canonical and re-encodes to check
  /// equality to what was decoded.
  fn read_canonical_E(mut reader: impl io::Read) -> io::Result<Self::E> {
    let mut bytes = <Self::E as GroupEncoding>::Repr::default();
    reader.read_exact(bytes.as_mut())?;
    let res = Option::<Self::E>::from(Self::E::from_bytes(&bytes))
      .ok_or_else(|| io::Error::other("invalid encoding of E"))?;
    if res.to_bytes().as_ref() != bytes.as_ref() {
      Err(io::Error::other("non-canonical encoding of E"))?;
    }
    Ok(res)
  }

  /// Derive a scalar from an XOF.
  fn from_xof(xof: blake3::OutputReader) -> Self::F;
  /// Hash the message and reduce it into a scalar.
  fn hash_message(message: &[u8]) -> Self::F;
  /// Reduce the `x`-coordinate of a point into a scalar.
  fn x_coordinate(point: &Self::E) -> Self::F;
}

/// ECDSA over secp256k1.
#[cfg(feature = "secp256k1")]
pub struct Secp256k1<P: Primes>(PhantomData<P>);
#[cfg(feature = "secp256k1")]
impl<CG: Element, P: Primes> Parameters<CG> for Secp256k1<P> {
  type E = k256::ProjectivePoint;
  type F = k256::Scalar;

  type RoundOneProofs = Ccykc2023RoundOne<P>;
  type RoundTwoProofs = Ccykc2023RoundTwo<P>;

  fn from_xof(mut xof: blake3::OutputReader) -> Self::F {
    let mut bytes = [0; 64];
    xof.fill(&mut bytes);
    use k256::elliptic_curve::ops::Reduce;
    <k256::Scalar as Reduce<k256::elliptic_curve::bigint::U512>>::reduce_bytes(&bytes.into())
  }
  fn hash_message(message: &[u8]) -> Self::F {
    use sha2::{Digest, Sha256};
    use k256::elliptic_curve::ops::Reduce;
    <k256::Scalar as Reduce<k256::U256>>::reduce_bytes(
      &<[u8; 32]>::from(Sha256::digest(message)).into(),
    )
  }
  fn x_coordinate(point: &Self::E) -> Self::F {
    use k256::elliptic_curve::{ops::Reduce, point::AffineCoordinates};
    <k256::Scalar as Reduce<k256::U256>>::reduce_bytes(
      &<[u8; 32]>::from(point.to_affine().x()).into(),
    )
  }
}

/// ECDSA over secp256k1, without identifiable aborts.
#[cfg(feature = "secp256k1")]
pub struct Secp256k1NoIa<P: Primes>(PhantomData<P>);
#[cfg(feature = "secp256k1")]
impl<CG: Element, P: Primes> Parameters<CG> for Secp256k1NoIa<P> {
  type E = <Secp256k1<P> as Parameters<CG>>::E;
  type F = <Secp256k1<P> as Parameters<CG>>::F;

  type RoundOneProofs = <Secp256k1<P> as Parameters<CG>>::RoundOneProofs;
  type RoundTwoProofs = NoIdentifiableAborts;

  fn from_xof(xof: blake3::OutputReader) -> Self::F {
    <Secp256k1<P> as Parameters<CG>>::from_xof(xof)
  }
  fn hash_message(message: &[u8]) -> Self::F {
    <Secp256k1<P> as Parameters<CG>>::hash_message(message)
  }
  fn x_coordinate(point: &Self::E) -> Self::F {
    <Secp256k1<P> as Parameters<CG>>::x_coordinate(point)
  }
}
