use std::io;

use cshake::digest::XofReader;
use sha2::{Digest as _, Sha256};

use crypto_bigint::{Reduce as _, Encoding as _, U256};
use group::Group;
use p256::{
  elliptic_curve::{sec1::FromSec1Point as _, point::AffineCoordinates as _},
  Scalar, ProjectivePoint,
};

use crate::WrappedGroup;

/// A ciphersuite for the NIST P-256 elliptic curve.
pub struct P256;
impl WrappedGroup for P256 {
  type G = ProjectivePoint;
  type Up = U256;

  const DST: &[u8] = b"P-256";
  const BITS_OF_SECURITY: u16 = 128;

  type CShake = cshake::CShake128;

  fn generator_e() -> Self::G {
    ProjectivePoint::GENERATOR
  }

  fn point_from_canonical_bytes(mut transcript: impl io::Read) -> io::Result<ProjectivePoint> {
    let mut bytes = [0; 33];
    transcript.read_exact(&mut bytes[.. 1])?;
    if bytes[0] == 0 {
      return Ok(ProjectivePoint::IDENTITY);
    }
    transcript.read_exact(&mut bytes[1 ..])?;
    ProjectivePoint::from_sec1_bytes(&bytes).map_err(io::Error::other)
  }

  fn x_coordinate(point: &Self::G) -> <Self::G as Group>::Scalar {
    Scalar::reduce(&U256::from_be_bytes(point.to_affine().x().into()))
  }

  // TODO: FIPS leaves this unspecified, solely with approved options
  fn hash_message(message: impl AsRef<[u8]>) -> Scalar {
    Scalar::reduce(&U256::from_be_bytes(Sha256::digest(message.as_ref()).into()))
  }

  fn squeeze_scalar(xof: &mut impl XofReader) -> Scalar {
    let mut bytes = [0; 64];
    xof.read(&mut bytes);
    let u255 = Scalar::reduce(&(U256::ONE << 255));
    let u256 = u255 + u255;
    Scalar::reduce(&U256::from_le_slice(&bytes[.. 32])) +
      (u256 * Scalar::reduce(&U256::from_le_slice(&bytes[32 ..])))
  }
}
