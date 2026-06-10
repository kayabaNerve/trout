use core::ops::Deref as _;
use alloc::{vec::Vec, vec};
use std::io;

use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};
use rand::CryptoRng;

use group::{ff::Field as _, Group, GroupEncoding as _};

use crypto_bigint::{CtAssign, Limb, Encoding, BoxedUint};
use class_groups::{NegativeDiscriminant as _, Element};

use cshake::digest::{CustomizedInit as _, Update as _, ExtendableOutput as _};

#[rustfmt::skip]
use crate::{CopyRead, WrappedGroup, Up2, NonInteractiveSetup, BatchVerifier, Ciphertext, Commitment};

/// The opening for a preprocess.
///
/// This MUST only be used once, even if the signing protocol it's used in aborts and does not
/// complete. The caller is wholly liable to ensure preprocesses are never reused.
pub struct PreprocessOpening {
  pub(crate) ciphertext_opening: Zeroizing<BoxedUint>,
  pub(crate) commitment_opening: Zeroizing<BoxedUint>,
}
impl Zeroize for PreprocessOpening {
  fn zeroize(&mut self) {
    let Self { ciphertext_opening, commitment_opening } = self;
    ciphertext_opening.zeroize();
    commitment_opening.zeroize();
  }
}
impl Drop for PreprocessOpening {
  fn drop(&mut self) {
    self.zeroize();
  }
}
impl ZeroizeOnDrop for PreprocessOpening {}

/// The key-, message-, and signing-set- independent first round of the Trout++ signing protocol.
pub struct Preprocess<E> {
  pub(crate) message: Vec<u8>,
  pub(crate) ciphertext: Ciphertext<E>,
  pub(crate) commitment: Commitment<E>,
}

impl<E: CtAssign + Element> Preprocess<E> {
  /// Participate in the first round of the Trout++ signing protocol.
  pub fn participate<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, G: WrappedGroup>(
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    mut out: impl io::Write,
  ) -> io::Result<PreprocessOpening> {
    let nonce = Zeroizing::new(<G::G as Group>::Scalar::random(&mut rng));
    let nonce_commitment = G::generator_e() * nonce.deref();

    let mut transcript = vec![];

    let (ciphertext, interactive_ciphertext) =
      Ciphertext::<E>::encrypt::<_, _, G>(&mut rng, setup, nonce.clone(), &mut transcript)?;
    let (commitment, interactive_commitment) =
      Commitment::<E>::commit::<Udk, Udp, G>(&mut rng, setup, &mut transcript)?;

    let opening = {
      let nonce_commitment = nonce_commitment.to_bytes();
      let nonce_commitment = nonce_commitment.as_ref();
      let ciphertext = {
        let mut bytes = vec![];
        ciphertext.clone().write(&mut bytes)?;
        bytes
      };
      let commitment = {
        let mut bytes = vec![];
        commitment.clone().write(&mut bytes)?;
        bytes
      };

      let mut sponge = G::CShake::new_customized(setup.context());
      sponge.update(nonce_commitment);
      sponge.update(&ciphertext);
      sponge.update(&commitment);
      sponge.update(&transcript);
      let mut sponge = sponge.finalize_xof();
      let (prime, challenge) = crate::challenge::<G>(&mut rng, &mut sponge);

      out.write_all(nonce_commitment)?;
      out.write_all(&ciphertext)?;
      out.write_all(&commitment)?;
      out.write_all(&transcript)?;

      let ciphertext_opening = interactive_ciphertext.respond(&prime, challenge, &mut out)?;
      let commitment_opening = interactive_commitment.respond::<G>(&prime, challenge, &mut out)?;

      PreprocessOpening { ciphertext_opening, commitment_opening }
    };

    Ok(opening)
  }
}

/// An in-progress aggregation of preprocesses.
pub struct Aggregating<'a, Udk, Udp, E, G: WrappedGroup> {
  setup: &'a NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
  batch_verifier: BatchVerifier<E, G>,
  sponge: G::CShake,
  nonce_commitment: G::G,
  ciphertext: Ciphertext<E>,
  commitment: Commitment<E>,
}

impl<'a, Udk: Encoding, Udp: Encoding, E: Element, G: WrappedGroup>
  Aggregating<'a, Udk, Udp, E, G>
{
  /// Begin aggregation of preprocesses.
  pub fn new(setup: &'a NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>) -> Self {
    let identity_p = E::identity(setup.cl15p().absolute_value());
    let identity_k = E::identity(setup.cl15p().fundamental_discriminant().absolute_value());

    Self {
      setup,
      batch_verifier: BatchVerifier::new(),
      sponge: G::CShake::new_customized(setup.context()),
      nonce_commitment: <G::G as Group>::identity(),
      ciphertext: Ciphertext { ciphertext: identity_p },
      commitment: Commitment { commitment: identity_k },
    }
  }
}

impl<Udk: Encoding, Udp: Encoding, E: Element, G: WrappedGroup> Aggregating<'_, Udk, Udp, E, G> {
  /// Aggregate the next preprocess.
  ///
  /// This is an order-dependent operation. Participants MUST have a consistent ordering.
  ///
  /// This MUST be done locally. It is unsafe to delegate aggregation to a third-party coordinator.
  ///
  /// An amount of preprocesses corresponding to the threshold MUST be aggregated. If the entities
  /// whose preprocesses were aggregated are compromised, they will be able to recover the private
  /// key from the resulting signature. This implementation's API does NOT enforce the preprocesses
  /// originate from the threshold amount of parties however to allow optimizing around the
  /// edge-case where one participant has multiple key shares (and therefore multiple preprocesses
  /// from them are redundant).
  ///
  /// If this errors, `self` will be left unmodified.
  pub fn aggregate(
    &mut self,
    mut rng: impl CryptoRng,
    read: impl io::Read,
  ) -> io::Result<Preprocess<E>> {
    let mut read = CopyRead { read, copy_to: vec![] };

    let nonce_commitment = G::point_from_canonical_bytes(&mut read)?;
    let ciphertext = Ciphertext::read(self.setup.cl15p(), &mut read)?;
    let commitment = Commitment::read(self.setup.cl15p(), &mut read)?;

    {
      let ciphertext_commit = crate::ciphertext::Commit::read(self.setup, &mut read)?;
      let commitment_commit = crate::commitment::Commit::read(self.setup, &mut read)?;

      let mut sponge = G::CShake::new_customized(self.setup.context());
      sponge.update(&read.copy_to);
      let mut sponge = sponge.finalize_xof();
      let (prime, challenge) = crate::challenge::<G>(&mut rng, &mut sponge);

      ciphertext_commit.queue_batch_verification(
        &mut rng,
        self.setup,
        &mut self.batch_verifier,
        ciphertext.clone(),
        nonce_commitment,
        &prime,
        challenge,
        &mut read,
      )?;
      commitment_commit.queue_batch_verification(
        &mut rng,
        self.setup,
        &mut self.batch_verifier,
        &commitment,
        prime,
        challenge,
        &mut read,
      )?;
    }

    self.sponge.update(&read.copy_to);
    self.nonce_commitment += nonce_commitment;
    self.ciphertext.ciphertext =
      self.ciphertext.ciphertext.clone().add(ciphertext.ciphertext.clone());
    self.commitment.commitment =
      self.commitment.commitment.clone().add(commitment.commitment.clone());

    Ok(Preprocess { message: read.copy_to, ciphertext, commitment })
  }
}

/// The result of the key-, message-, and signing-set- independent first round of Trout++.
pub struct AggregatePreprocess<E, G: WrappedGroup> {
  pub(crate) sponge: G::CShake,
  pub(crate) nonce_commitment: G::G,
  pub(crate) ciphertext: Ciphertext<E>,
  pub(crate) commitment: Commitment<E>,
}

impl<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, E: Element, G: WrappedGroup>
  Aggregating<'_, Udk, Udp, E, G>
{
  /// Verify the first round of preprocesses.
  ///
  /// This does not identify _which_ preprocess was invalid if an error occurs. The caller, if
  /// interested, must verify the preprocesses individually to find that out.
  pub fn verify(self) -> io::Result<AggregatePreprocess<E, G>> {
    let Self { setup, batch_verifier, sponge, nonce_commitment, ciphertext, commitment } = self;
    let () = batch_verifier.verify(setup)?;
    Ok(AggregatePreprocess { sponge, nonce_commitment, ciphertext, commitment })
  }
}
