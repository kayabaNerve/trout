use alloc::vec;
use std::io;

use zeroize::{Zeroize as _, ZeroizeOnDrop, Zeroizing};
use rand::CryptoRng;

use group::{ff::PrimeField as _, Group};

use crypto_bigint::{
  CtAssign, NonZero, ConcatenatingMul as _, BitOps, Encoding, RandomBits as _, Resize as _,
  BoxedUint,
};
use class_groups::{NegativeDiscriminant as _, Element, Cl15p, Table};

use crate::{WrappedGroup, Up2, NonInteractiveSetup, BatchVerifier};

/// A statistically-hiding computationally-binding to a value modulo `p`.
///
/// This is formally defined as an element of the class group with discriminant $\Delta_k$ and
/// encoded accordingly.
#[derive(Clone)]
pub(crate) struct Commitment<E> {
  pub(crate) commitment: E,
}

/// The commitment for the proof of knowledge.
pub(crate) struct Commit<E> {
  R_commitment: E,
}

/// A commitment actively engaged in an interactive proof of knowledge.
///
/// This code models the proof of knowledge as an interactive protocol despite using the
/// Fiat-Shamir transform. The intent is for the caller to simultaneously commit for all proofs
/// they will perform this round, before deriving a single set of challenges from the transcript,
/// and the proofs calculating their responses. This is a non-trivial optimization as the
/// challenges are a result of a hash-to-prime function.
pub(crate) struct InteractiveCommitment<E> {
  identity_k: E,
  generator_k: Table<E>,
  r_commitment: BoxedUint,
  beta: BoxedUint,
}

impl<E> Drop for InteractiveCommitment<E> {
  /// This will zeroize every secret contained within this.
  fn drop(&mut self) {
    let Self { identity_k: _, generator_k: _, r_commitment, beta } = self;
    r_commitment.zeroize();
    beta.zeroize();
  }
}
impl<E> ZeroizeOnDrop for InteractiveCommitment<E> {}

impl<E: CtAssign + Element> Commitment<E> {
  /// Commit to a value modulo `p`.
  ///
  /// This does not accept the value as input but samples one from uniform.
  ///
  /// This will write the commitment for the proof of knowledge to the transcript.
  pub(crate) fn commit<Udk: Encoding, Udp, G: WrappedGroup>(
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    mut transcript: impl io::Write,
  ) -> io::Result<(Commitment<E>, InteractiveCommitment<E>)> {
    const STATISTICAL_DISTANCE_FROM_UNIFORM: u32 = 128;

    // We represent `beta * q + b` as the singular `beta` value
    let beta = BoxedUint::random_bits(
      &mut rng,
      STATISTICAL_DISTANCE_FROM_UNIFORM +
        <G::G as Group>::Scalar::NUM_BITS +
        setup.cl15p().fundamental_discriminant().upper_bound_on_order(),
    );

    let prime_bits = 8 * setup.cl15p().fundamental_discriminant().p().bits().div_ceil(8);
    let r_commitment = BoxedUint::random_bits(
      &mut rng,
      STATISTICAL_DISTANCE_FROM_UNIFORM +
        prime_bits +
        setup.cl15p().fundamental_discriminant().upper_bound_on_order(),
    );

    // TODO
    let identity_k = E::identity(setup.cl15p().fundamental_discriminant().absolute_value());
    let generator_k =
      Table::new(core::num::NonZero::new(6).unwrap(), E::from(setup.generator_k().clone()));

    let commitment = Commitment {
      commitment: Table::msm(
        &identity_k,
        &[(Zeroizing::new(beta.to_le_bytes()).as_ref(), &generator_k)],
      ),
    };

    let R_commitment = Table::msm(
      &identity_k,
      &[(Zeroizing::new(r_commitment.to_le_bytes()).as_ref(), &generator_k)],
    );

    let interactive_commitment =
      InteractiveCommitment { identity_k, generator_k, r_commitment, beta };

    R_commitment.compress(&mut transcript)?;

    Ok((commitment, interactive_commitment))
  }
}

impl<E: Element> Commitment<E> {
  /// Write the commitment to the transcript.
  pub(crate) fn write(self, transcript: impl io::Write) -> io::Result<()> {
    self.commitment.compress(transcript)
  }

  /// Read a commitment from the transcript.
  pub(crate) fn read<Up: BitOps, Up2, Udk: Encoding, Udp: Encoding>(
    cl15p: &Cl15p<Up, Up2, Udk, Udp>,
    transcript: impl io::Read,
  ) -> io::Result<Self> {
    Ok(Self {
      commitment: E::decompress(transcript, cl15p.fundamental_discriminant().absolute_value())?,
    })
  }
}

impl<E: CtAssign + Element> InteractiveCommitment<E> {
  /// Respond to the challenge for the proof of knowledge.
  ///
  /// This will write the response to the transcript and return the opening of the commitment.
  pub(crate) fn respond<G: WrappedGroup>(
    self,
    prime: &BoxedUint,
    challenge: <G::G as Group>::Scalar,
    mut transcript: impl io::Write,
  ) -> io::Result<Zeroizing<BoxedUint>> {
    // `r_commitment + c * beta`
    let s_beta = Zeroizing::new(self.r_commitment.concatenating_add(Zeroizing::new(
      crate::Up_from_scalar::<BoxedUint, G>(&challenge).concatenating_mul(&self.beta),
    )));

    let divisor = NonZero::new(prime.clone()).expect("a prime number is non-zero");
    let (d, e) = s_beta.div_rem(&divisor);
    let d = Zeroizing::new(d);

    Table::msm(&self.identity_k, &[(Zeroizing::new(d.to_le_bytes()).as_ref(), &self.generator_k)])
      .compress(&mut transcript)?;
    transcript.write_all(
      &e.to_le_bytes()[.. usize::try_from(<G::G as Group>::Scalar::NUM_BITS.div_ceil(8)).unwrap()],
    )?;

    Ok(Zeroizing::new(self.beta.clone()))
  }
}

impl<E: Element> Commit<E> {
  /// Read the commitment from the proof of knowledge from the transcript.
  pub(crate) fn read<Up: BitOps, Up2, Udk: Encoding, Udp: Encoding>(
    setup: &NonInteractiveSetup<Up, Up2, Udk, Udp>,
    mut transcript: impl io::Read,
  ) -> io::Result<Self> {
    let R_commitment =
      E::decompress(&mut transcript, setup.cl15p().fundamental_discriminant().absolute_value())?;
    Ok(Self { R_commitment })
  }

  /// Check the response (read from the transcript) to the challenge.
  ///
  /// If this errors, `batch_verifier` will be left unmodified.
  pub(crate) fn queue_batch_verification<Udk: Encoding, Udp: Encoding, G: WrappedGroup>(
    self,
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    batch_verifier: &mut BatchVerifier<E, G>,
    commitment: &Commitment<E>,
    prime: BoxedUint,
    challenge: <G::G as Group>::Scalar,
    mut transcript: impl io::Read,
  ) -> io::Result<()> {
    let Self { R_commitment } = self;

    let D =
      E::decompress(&mut transcript, setup.cl15p().fundamental_discriminant().absolute_value())?;

    let divisor = &prime;
    let e = {
      let mut e = vec![0; usize::try_from(divisor.bits_precision().div_ceil(8)).unwrap()];
      transcript.read_exact(&mut e)?;
      let e = BoxedUint::from_le_bytes(e.into());
      if e >= divisor {
        Err(io::Error::other(r"$e \ge c_\mathsf{prime}$"))?;
      }
      e
    };

    // `R_commitment + c commitment == prime D + e generator_k`
    {
      let batch_verification_weight = BoxedUint::random_bits(&mut rng, 128);

      batch_verifier.generator_k = batch_verifier
        .generator_k
        .concatenating_add(batch_verification_weight.concatenating_mul(e));
      // If we unnecessarily widened `batch_verifier.generator_k`, resize it back down
      batch_verifier.generator_k =
        batch_verifier.generator_k.clone().resize(batch_verifier.generator_k.bits_vartime());

      // TODO: `Table::new`
      batch_verifier.k.extend([
        (
          batch_verification_weight.concatenating_mul(divisor),
          Table::new(core::num::NonZero::new(4).unwrap(), D),
        ),
        (
          batch_verification_weight
            .concatenating_mul(crate::Up_from_scalar::<BoxedUint, G>(&challenge)),
          Table::new(core::num::NonZero::new(4).unwrap(), -commitment.commitment.clone()),
        ),
        (batch_verification_weight, Table::new(core::num::NonZero::new(4).unwrap(), -R_commitment)),
      ]);
    }

    Ok(())
  }
}
