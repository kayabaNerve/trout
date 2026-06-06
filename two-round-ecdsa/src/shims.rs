use core::fmt;
use zeroize::Zeroize;
use group::{ff::PrimeField, Group};

/// The ID of a participant, defined as a non-zero u16.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Zeroize)]
pub struct Participant(u16);
impl Participant {
  /// Create a new Participant identifier from a u16.
  #[must_use]
  pub const fn new(i: u16) -> Option<Participant> {
    if i == 0 { None } else { Some(Participant(i)) }
  }

  /// Convert a Participant identifier to bytes.
  #[must_use]
  pub const fn to_bytes(&self) -> [u8; 2] {
    self.0.to_le_bytes()
  }

  /// Create an iterator over participant indexes.
  pub fn iter() -> impl Iterator<Item = Participant> {
    struct ParticipantIterator(u16);
    impl Iterator for ParticipantIterator {
      type Item = Participant;
      fn next(&mut self) -> Option<Self::Item> {
        self.0 = self.0.checked_add(1)?;
        Some(Participant(self.0))
      }
    }
    ParticipantIterator(0)
  }
}

impl From<Participant> for u16 {
  fn from(participant: Participant) -> u16 {
    participant.0
  }
}

impl fmt::Display for Participant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}

pub(crate) fn multiexp_vartime<G: Group<Scalar: PrimeFieldBits>>(pairs: &[(G::Scalar, G)]) -> G {
  pairs.iter().map(|(scalar, point)| *point * scalar).sum()
}

/// [`group::ff::PrimeFieldBits`] but re-defined here so it may be implemented over `k256::Scalar`
pub trait PrimeFieldBits: PrimeField {
  /// The representation of the bits
  type ReprBits: Send + Sync + group::ff::BitViewSized;
  /// The little-endian bits representing this field element
  fn to_le_bits(&self) -> Self::ReprBits;
}
#[cfg(feature = "secp256k1")]
impl PrimeFieldBits for k256::Scalar {
  type ReprBits = [u8; 32];
  fn to_le_bits(&self) -> Self::ReprBits {
    let mut repr = <[u8; 32]>::from(self.to_repr());
    repr.reverse();
    repr
  }
}
