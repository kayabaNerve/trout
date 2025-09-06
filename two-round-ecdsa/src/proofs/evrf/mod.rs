use std::io::{self, Write};

use zeroize::Zeroizing;
use rand::CryptoRng;

use group::{ff::Field, Group, GroupEncoding};
use class_groups::Element;

/// The DDH-premised eVRF.
pub mod ddh;
pub(crate) use ddh::*;

use crate::{DigestReader, DigestWriter, Parameters};

/// An eVRF.
///
/// The [eVRF paper](https://eprint.iacr.org/2024/996) details two constructions, one premised on
/// Paillier and one premised on the EC DDH problem. There are also two alternative constructions
/// posited since:
/// - The EC DDH eVRF, optimized by using the function field of the EC to prove scalar
///   multiplications ([as posited by Eagen](https://eprint.iacr.org/2022/596))
/// - [An LWR-based construction](https://eprint.iacr.org/2024/996)
///
/// The eVRF used is left to the choice of the caller.
pub trait Evrf<CG: Element, P: Parameters<CG>> {
  /// A global setup for invocations of the eVRF.
  type GlobalSetup: Clone;
  /// The view of someone's setup, as necessary to verify someone's invocation of the eVRF.
  type SetupView: Clone;
  /// The setup, as necessary to invoke the eVRF.
  type Setup;
  /// The context for an eVRF invocation.
  type Context;
  /// The batch verifier for eVRFs.
  type BatchVerifier;

  /// Perform the global setup for the eVRF.
  fn global_setup() -> Self::GlobalSetup;

  /// Perform the per-participant setup for the eVRF.
  fn setup(
    global_setup: &Self::GlobalSetup,
    rng: &mut impl CryptoRng,
  ) -> (Self::SetupView, Self::Setup);

  /// Create the context for the eVRF invocation.
  ///
  /// If this function draws from the transcript, it MUST also advance it to ensure future draws
  /// don't yield the same values.
  fn context(global_setup: &Self::GlobalSetup, transcript: &mut blake3::Hasher) -> Self::Context;

  /// Invoke the eVRF to obtain a random value.
  ///
  /// The context MUST be binding to the setup and the invocation. This allows the eVRF
  /// implementation to not have to transcript these itself.
  ///
  /// The proof is written to `proof`. If this function returns an error, the status of `proof` is
  /// undefined.
  fn prove<W: io::Write>(
    rng: &mut impl CryptoRng,
    global_setup: &Self::GlobalSetup,
    setup: &Self::Setup,
    context: &Self::Context,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<Zeroizing<P::F>>;

  /// Create a batch verifier of eVRFs.
  fn batch_verifier(global_setup: &Self::GlobalSetup) -> Self::BatchVerifier;
  /// Queue verification of someone's invocation of the eVRF.
  ///
  /// Returns the commitment to the value over the generator of the elliptic curve. This commitment
  /// is not guaranteed to be verified at this time. The batch verifier must be verified for this
  /// item to be verified.
  ///
  /// If an error is returned, `proof` is left in an undefined state. The batch verifier is
  /// guaranteed to not be mutated however, meaning a proof which raises an error while being
  /// queued will not corrupt the batch verifier and will leave it eligible to verify other proofs.
  fn queue_verification<R: io::Read>(
    rng: &mut impl CryptoRng,
    global_setup: &Self::GlobalSetup,
    batch_verifier: &mut Self::BatchVerifier,
    participant: dkg::Participant,
    setup: &Self::SetupView,
    context: &Self::Context,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<P::E>;
  /// Verify all proofs within the batch verifier.
  ///
  /// Returns `Ok(())` or a list of *all* of the *faulty* participants.
  fn verify(
    global_setup: &Self::GlobalSetup,
    batch_verifier: Self::BatchVerifier,
  ) -> Result<(), Vec<dkg::Participant>>;
}

/// A dummy eVRF which does not perform any proof and accordingly isn't verifiable.
///
/// This is not presented as a secure choice of eVRF. Using this removes the ability to simulate
/// the nonce within the security proofs. This is presented solely for evaluation purposes or in
/// case future works prove the security of this scheme even without the eVRF (as
/// <https://eprint.iacr.org/2021/1449> implies the security of).
pub struct DummyEvrf;
impl<CG: Element, P: Parameters<CG>> Evrf<CG, P> for DummyEvrf {
  type GlobalSetup = ();
  type SetupView = ();
  type Setup = ();
  type Context = ();
  type BatchVerifier = ();

  fn global_setup() -> Self::GlobalSetup {}

  fn setup(
    _global_setup: &Self::GlobalSetup,
    _rng: &mut impl CryptoRng,
  ) -> (Self::SetupView, Self::Setup) {
    ((), ())
  }

  fn context(_global_setup: &Self::GlobalSetup, _transcript: &mut blake3::Hasher) -> Self::Context {
  }

  fn batch_verifier(_global_setup: &Self::GlobalSetup) -> Self::BatchVerifier {}

  fn prove<W: io::Write>(
    rng: &mut impl CryptoRng,
    _global_setup: &Self::GlobalSetup,
    _setup: &Self::Setup,
    _context: &Self::Context,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<Zeroizing<P::F>> {
    let nonce = Zeroizing::new(P::F::random(rng));
    let nonce_commitment = P::E::generator() * *nonce;
    transcript.write_all(nonce_commitment.to_bytes().as_ref())?;
    Ok(nonce)
  }

  fn queue_verification<R: io::Read>(
    _rng: &mut impl CryptoRng,
    _global_setup: &Self::GlobalSetup,
    _batch_verifier: &mut Self::BatchVerifier,
    _participant: dkg::Participant,
    _setup: &Self::SetupView,
    _context: &Self::Context,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<P::E> {
    P::read_canonical_E(transcript)
  }

  fn verify(
    _global_setup: &Self::GlobalSetup,
    _batch_verifier: Self::BatchVerifier,
  ) -> Result<(), Vec<dkg::Participant>> {
    Ok(())
  }
}
