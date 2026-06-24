use core::ops::Deref as _;
use alloc::{vec::Vec, vec};
use std::io::{self, Write as _};

use zeroize::Zeroizing;
use rand::CryptoRng;

use group::{ff::PrimeField as _, Group, GroupEncoding as _};

use crypto_bigint::{CtAssign, CtSelect, Limb, ConcatenatingMul as _, Encoding, BoxedUint};

use class_groups::{NegativeDiscriminant as _, Element, Table};

use cshake::digest::{CustomizedInit as _, Update as _, ExtendableOutput as _};

use crate::{CopyRead, WrappedGroup, Up2, NonInteractiveSetup, BatchVerifier, Ciphertext};

mod sealed {
  pub(super) trait Sealed {}
}

/// A view over an ECDSA signing key, as required by the Trout++ signing protocol.
#[expect(private_bounds)]
pub trait SigningKey<E, G: WrappedGroup>: sealed::Sealed {
  /// The setup this corresponds to.
  type Setup;

  /// The type of the opening for the setup this corresponds to.
  type Opening;

  /// The transcript for this signing key.
  ///
  /// The transcript MUST be binding to all the individual ciphertexts which contribute to the
  /// resulting ciphertext AND any derivations applied.
  fn transcript(&self) -> G::CShake;

  /// The signing key.
  fn key(&self) -> G::G;

  /// The ciphertext for the discrete logarithm of the signing key.
  fn ciphertext(&self) -> E;

  /// Transform an individual share's setup to the corresponding share of this key's ciphertext.
  // TODO: Support multiple key shares which belong to a single identity
  fn share_ciphertext(
    &self,
    interpolation_factor: <G::G as Group>::Scalar,
    setup: Self::Setup,
  ) -> E;

  /// Transform an individual share's opening to the corresponding share of this key's ciphertext's
  /// opening.
  // TODO: Support multiple key shares which belong to a single identity
  fn share_opening(
    &self,
    interpolation_factor: <G::G as Group>::Scalar,
    share: Self::Opening,
  ) -> Zeroizing<BoxedUint>;
}

/// The interactive setup for the Trout++ signing protocol.
///
/// This inputs a Shamir secret share of an ECDSA signing key. Protocols for generating
/// ECDSA signing keys are out of scope to this library (and Trout++'s technical specification as a
/// whole), intending to be composed with existing (ideally standardized) key generation protocols.
/// We do assume an _unbiased_ key generation protocol.
///
/// This MAY be run before the signing protocol or MAY be run in parallel with the first round of
/// the signing protocol. This SHOULD be run ahead of time in order to reduce the communication
/// cost of the signing protocol but the resulting protocol has the same complexities either way.
#[derive(Clone)]
pub struct InteractiveSetup<E> {
  ciphertext: Ciphertext<E>,
  message: Vec<u8>,
}

impl<E: CtAssign + Element> InteractiveSetup<E> {
  /// Perform the setup protocol.
  pub fn setup<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, G: WrappedGroup>(
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    share: Zeroizing<<G::G as Group>::Scalar>,
    mut out: impl io::Write,
  ) -> io::Result<(Self, Zeroizing<BoxedUint>)> {
    let mut commit = vec![];
    let (ciphertext, interactive_ciphertext) =
      Ciphertext::<E>::encrypt::<_, _, G>(&mut rng, setup, share.clone(), &mut commit)?;

    let mut message = vec![];
    ciphertext.clone().write(&mut message)?;
    message.write_all(&commit)?;

    let mut sponge = G::CShake::new_customized(setup.context());
    sponge.update((G::generator_e() * share.deref()).to_bytes().as_ref());
    sponge.update(&message);
    let mut sponge = sponge.finalize_xof();

    let (prime, challenge) = crate::challenge::<G>(&mut rng, &mut sponge);
    let opening = interactive_ciphertext.respond(&prime, challenge, &mut message)?;

    out.write_all(&message)?;

    Ok((Self { ciphertext, message }, opening))
  }
}

impl<E: Element> InteractiveSetup<E> {
  /// Deserialize and verify an invocation of the setup.
  // TODO: Support batch verification
  pub fn verify<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, G: WrappedGroup>(
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    elliptic_commitment: G::G,
    input: impl io::Read,
  ) -> io::Result<Self> {
    let mut sponge = G::CShake::new_customized(setup.context());
    sponge.update(elliptic_commitment.to_bytes().as_ref());

    let mut input = CopyRead { read: input, copy_to: vec![] };

    let ciphertext = Ciphertext::read(setup.cl15p(), &mut input)?;
    let commit = crate::ciphertext::Commit::<E, G>::read(setup, &mut input)?;

    sponge.update(&input.copy_to);
    let mut sponge = sponge.finalize_xof();
    let (prime, challenge) = crate::challenge::<G>(&mut rng, &mut sponge);

    let mut batch_verifier = BatchVerifier::new();
    let () = commit.queue_batch_verification(
      &mut rng,
      setup,
      &mut batch_verifier,
      ciphertext.clone(),
      elliptic_commitment,
      &prime,
      challenge,
      &mut input,
    )?;
    let () = batch_verifier.verify(setup)?;

    Ok(Self { ciphertext, message: input.copy_to })
  }
}

struct SigningKeyWithoutDerivations<E, G: WrappedGroup> {
  transcript: G::CShake,
  key: G::G,
  ciphertext: E,
}

impl<E: Element, G: WrappedGroup> sealed::Sealed for SigningKeyWithoutDerivations<E, G> {}
impl<E: Element, G: WrappedGroup> SigningKey<E, G> for SigningKeyWithoutDerivations<E, G> {
  type Setup = InteractiveSetup<E>;
  type Opening = Zeroizing<BoxedUint>;
  fn transcript(&self) -> G::CShake {
    self.transcript.clone()
  }
  fn key(&self) -> G::G {
    self.key
  }
  fn ciphertext(&self) -> E {
    self.ciphertext.clone()
  }
  fn share_ciphertext(
    &self,
    interpolation_factor: <G::G as Group>::Scalar,
    setup: Self::Setup,
  ) -> E {
    // TODO
    let (_a, _b, _c, discriminant_abs) = setup.ciphertext.ciphertext.clone().a_b_c_discriminant();
    let ciphertext = Table::new(core::num::NonZero::new(4).unwrap(), setup.ciphertext.ciphertext);
    Table::msm_vartime(
      E::identity(discriminant_abs),
      &[(
        crate::Up_from_scalar::<BoxedUint, G>(interpolation_factor).to_le_bytes().as_ref(),
        &ciphertext,
      )],
    )
  }
  fn share_opening(
    &self,
    interpolation_factor: <G::G as Group>::Scalar,
    opening: Self::Opening,
  ) -> Zeroizing<BoxedUint> {
    Zeroizing::new(
      opening.concatenating_mul(crate::Up_from_scalar::<BoxedUint, G>(interpolation_factor)),
    )
  }
}

impl<E: Element> InteractiveSetup<E> {
  /// The representation of the signing key for the sum of these setups.
  ///
  /// The `key` MUST be the key specified as the context string for the non-interactive setup.
  ///
  /// Each setup is specified with a scalar which SHOULD be its interpolation factor such that the
  /// sum of the ciphertexts encrypt the signing key. These will presumably be the Lagrange
  /// interpolation factors.
  pub fn signing_key<'a, Udk: Encoding, Udp: Encoding, G: WrappedGroup>(
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    key: G::G,
    setups: impl Iterator<Item = (<G::G as Group>::Scalar, &'a Self)>,
  ) -> impl SigningKey<E, G, Setup = Self, Opening = Zeroizing<BoxedUint>>
  where
    E: 'a,
  {
    let mut transcript = G::CShake::new_customized(setup.context());
    let cl15p = setup.cl15p();
    let mut ciphertext = E::identity(cl15p.absolute_value());
    for (interpolation_factor, setup) in setups {
      transcript.update(interpolation_factor.to_repr().as_ref());
      transcript.update(&setup.message);

      // TODO: Calculate this with a multi-scalar multiplication
      let table =
        Table::new(core::num::NonZero::new(4).unwrap(), setup.ciphertext.ciphertext.clone());
      ciphertext = ciphertext.add(Table::msm_vartime(
        E::identity(cl15p.absolute_value()),
        &[(
          crate::Up_from_scalar::<BoxedUint, G>(interpolation_factor).to_le_bytes().as_ref(),
          &table,
        )],
      ));
    }
    SigningKeyWithoutDerivations { transcript, key, ciphertext }
  }
}

/// The interactive setup for the Trout++ signing protocol _with support for additive key
/// derivations_.
///
/// This inputs two Shamir secret shares which may have a linear combination taking to yield an
/// ECDSA signing key. Protocols for sharing secrets are out of scope to this library (and
/// Trout++'s technical specification as a whole), intending to be composed with existing (ideally
/// standardized) key generation protocols. We do assume an _unbiased_ key generation protocol.
///
/// This MAY be run before the signing protocol or MAY be run in parallel with the first round of
/// the signing protocol. This SHOULD be run ahead of time in order to reduce the communication
/// cost of the signing protocol but the resulting protocol has the same complexities either way.
#[derive(Clone)]
pub struct InteractiveSetupWithDerivations<E> {
  ciphertexts: [Ciphertext<E>; 2],
  message: Vec<u8>,
}

impl<E: CtSelect + CtAssign + Element> InteractiveSetupWithDerivations<E> {
  /// Perform the setup protocol with support for additive key derivations.
  pub fn setup<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, G: WrappedGroup>(
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    shares: Zeroizing<[<G::G as Group>::Scalar; 2]>,
    mut out: impl io::Write,
  ) -> io::Result<(Self, [Zeroizing<BoxedUint>; 2])> {
    let mut ciphertexts = Vec::with_capacity(2);
    let mut commit = vec![];
    let mut message = vec![];
    let interactive_ciphertexts = shares.map(|share| {
      let (ciphertext, interactive_ciphertext) =
        Ciphertext::<E>::encrypt::<_, _, G>(&mut rng, setup, Zeroizing::new(share), &mut commit)
          .expect("`<Vec<u8> as io::Write>::write` is infallible");
      ciphertext
        .clone()
        .write(&mut message)
        .expect("`<Vec<u8> as io::Write>::write` is infallible");
      ciphertexts.push(ciphertext);
      interactive_ciphertext
    });
    message.write_all(&commit)?;

    let mut sponge = G::CShake::new_customized(setup.context());
    sponge.update((G::generator_e() * shares.deref()[0]).to_bytes().as_ref());
    sponge.update((G::generator_e() * shares.deref()[1]).to_bytes().as_ref());
    sponge.update(&message);
    let mut sponge = sponge.finalize_xof();

    let (prime, challenge) = crate::challenge::<G>(&mut rng, &mut sponge);
    let openings = interactive_ciphertexts.map(|interactive_ciphertext| {
      interactive_ciphertext
        .respond(&prime, challenge, &mut message)
        .expect("`<Vec<u8> as io::Write>::write` is infallible")
    });

    out.write_all(&message)?;

    Ok((Self { ciphertexts: ciphertexts.try_into().map_err(|_| ()).unwrap(), message }, openings))
  }

  /// Deserialize and verify an invocation of the setup.
  // TODO: Support batch verification
  pub fn verify<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, G: WrappedGroup>(
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    elliptic_commitments: [G::G; 2],
    input: impl io::Read,
  ) -> io::Result<Self> {
    let mut sponge = G::CShake::new_customized(setup.context());
    for elliptic_commitment in elliptic_commitments {
      sponge.update(elliptic_commitment.to_bytes().as_ref());
    }

    let mut input = CopyRead { read: input, copy_to: vec![] };

    let ciphertexts = {
      let first_ciphertext = Ciphertext::read(setup.cl15p(), &mut input)?;
      let second_ciphertext = Ciphertext::read(setup.cl15p(), &mut input)?;
      [first_ciphertext, second_ciphertext]
    };
    let commits = {
      let first_commit = crate::ciphertext::Commit::<E, G>::read(setup, &mut input)?;
      let second_commit = crate::ciphertext::Commit::<E, G>::read(setup, &mut input)?;
      [first_commit, second_commit]
    };

    sponge.update(&input.copy_to);
    let mut sponge = sponge.finalize_xof();
    let (prime, challenge) = crate::challenge::<G>(&mut rng, &mut sponge);

    let mut batch_verifier = BatchVerifier::new();
    for ((elliptic_commitment, ciphertext), commit) in
      elliptic_commitments.into_iter().zip(ciphertexts.iter().cloned()).zip(commits)
    {
      let () = commit.queue_batch_verification(
        &mut rng,
        setup,
        &mut batch_verifier,
        ciphertext,
        elliptic_commitment,
        &prime,
        challenge,
        &mut input,
      )?;
    }
    let () = batch_verifier.verify(setup)?;

    Ok(Self { ciphertexts, message: input.copy_to })
  }
}

impl<E> InteractiveSetupWithDerivations<E> {
  fn scalars<G: WrappedGroup>(
    interpolation_factor: <G::G as Group>::Scalar,
    derivation: <G::G as Group>::Scalar,
  ) -> (BoxedUint, BoxedUint) {
    (
      crate::Up_from_scalar::<BoxedUint, G>(interpolation_factor),
      crate::Up_from_scalar::<BoxedUint, G>(derivation * interpolation_factor),
    )
  }
}

impl<E: Element> InteractiveSetupWithDerivations<E> {
  fn scaled_ciphertext<G: WrappedGroup>(
    self,
    interpolation_factor: <G::G as Group>::Scalar,
    derivation: <G::G as Group>::Scalar,
  ) -> E {
    // TODO
    let (_a, _b, _c, discriminant_abs) =
      self.ciphertexts[0].ciphertext.clone().a_b_c_discriminant();
    let [first_ciphertext, second_ciphertext] = self.ciphertexts;
    let first_ciphertext =
      Table::new(core::num::NonZero::new(4).unwrap(), first_ciphertext.ciphertext);
    let second_ciphertext =
      Table::new(core::num::NonZero::new(4).unwrap(), second_ciphertext.ciphertext);
    let scalars = Self::scalars::<G>(interpolation_factor, derivation);
    Table::msm_vartime(
      E::identity(discriminant_abs),
      &[
        (scalars.0.to_le_bytes().as_ref(), &first_ciphertext),
        (scalars.1.to_le_bytes().as_ref(), &second_ciphertext),
      ],
    )
  }
}

struct SigningKeyWithDerivations<E, G: WrappedGroup> {
  derivation: <G::G as Group>::Scalar,
  transcript: G::CShake,
  key: G::G,
  ciphertext: E,
}

impl<E: Element, G: WrappedGroup> sealed::Sealed for SigningKeyWithDerivations<E, G> {}
impl<E: Element, G: WrappedGroup> SigningKey<E, G> for SigningKeyWithDerivations<E, G> {
  type Setup = InteractiveSetupWithDerivations<E>;
  type Opening = Zeroizing<[BoxedUint; 2]>;
  fn transcript(&self) -> G::CShake {
    self.transcript.clone()
  }
  fn key(&self) -> G::G {
    self.key
  }
  fn ciphertext(&self) -> E {
    self.ciphertext.clone()
  }
  fn share_ciphertext(
    &self,
    interpolation_factor: <G::G as Group>::Scalar,
    setup: Self::Setup,
  ) -> E {
    setup.scaled_ciphertext::<G>(interpolation_factor, self.derivation)
  }
  fn share_opening(
    &self,
    interpolation_factor: <G::G as Group>::Scalar,
    share: Self::Opening,
  ) -> Zeroizing<BoxedUint> {
    let scalars =
      InteractiveSetupWithDerivations::<E>::scalars::<G>(interpolation_factor, self.derivation);
    Zeroizing::new(
      share[0]
        .concatenating_mul(scalars.0)
        .concatenating_add(share[1].concatenating_mul(scalars.1)),
    )
  }
}

impl<E: Element> InteractiveSetupWithDerivations<E> {
  /// The representation of the signing key for the sum of these setups.
  ///
  /// `key` MUST be the terms specified as the context string for the non-interactive setup.
  ///
  /// Each setup is specified with a scalar which SHOULD be its interpolation factor such that the
  /// sum of the ciphertexts encrypt the signing key. These will presumably be the Lagrange
  /// interpolation factors.
  pub fn signing_key<'a, Udk: Encoding, Udp: Encoding, G: WrappedGroup>(
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    key: [G::G; 2],
    setups: impl Iterator<Item = (<G::G as Group>::Scalar, &'a Self)>,
    derivation: <G::G as Group>::Scalar,
  ) -> impl SigningKey<E, G, Setup = Self, Opening = Zeroizing<[BoxedUint; 2]>>
  where
    E: 'a,
  {
    let mut transcript = G::CShake::new_customized(setup.context());
    transcript.update(derivation.to_repr().as_ref());
    let cl15p = setup.cl15p();
    let mut ciphertext = E::identity(cl15p.absolute_value());
    for (interpolation_factor, setup) in setups {
      transcript.update(interpolation_factor.to_repr().as_ref());
      transcript.update(&setup.message);

      // TODO: Calculate this with a multi-scalar multiplication
      ciphertext =
        ciphertext.add(setup.clone().scaled_ciphertext::<G>(interpolation_factor, derivation));
    }

    SigningKeyWithDerivations {
      derivation,
      transcript,
      key: key[0] + (key[1] * derivation),
      ciphertext,
    }
  }
}
