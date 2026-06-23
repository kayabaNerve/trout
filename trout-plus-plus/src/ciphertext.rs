use core::ops::Deref as _;
use alloc::vec;
use std::io;

use zeroize::{Zeroize as _, ZeroizeOnDrop, Zeroizing};
use rand::CryptoRng;

use group::{
  ff::{Field as _, PrimeField},
  Group, GroupEncoding as _,
};

use crypto_bigint::{
  CtAssign, NonZero, Limb, ConcatenatingMul as _, BitOps, Encoding, RandomBits as _, Resize as _,
  BoxedUint,
};
use class_groups::{NegativeDiscriminant as _, Element, Cl15p, Table};

use crate::{WrappedGroup, Up2, NonInteractiveSetup, BatchVerifier};

/// A symmetric ciphertext indistinguishable under the Hard Subgroup Membership assumption.
///
/// This explicitly encrypts a discrete logarithm of an elliptic curve point whose order is equal
/// to `p`.
///
/// This is formally defined as an element of the class group with discriminant $\Delta_p$ and
/// encoded accordingly.
#[derive(Clone)]
pub(crate) struct Ciphertext<E> {
  pub(crate) ciphertext: E,
}

/// The commitment for the proof of knowledge.
pub(crate) struct Commit<E, G: WrappedGroup> {
  R_ciphertext: E,
  R_elliptic: G::G,
}

/// A symmetric ciphertext actively engaged in an interactive proof of knowledge.
///
/// This code models the proof of knowledge as an interactive protocol despite using the
/// Fiat-Shamir transform. The intent is for the caller to simultaneously commit for all proofs
/// they will perform this round, before deriving a single set of challenges from the transcript,
/// and the proofs calculating their responses. This is a non-trivial optimization as the
/// challenges are a result of a hash-to-prime function.
pub(crate) struct InteractiveCiphertext<'cl15p, Udk, Udp, E, G: WrappedGroup> {
  cl15p: &'cl15p Cl15p<G::Up, Up2<G>, Udk, Udp>,
  identity_p: E,
  generator_p: Table<E>,
  r_ciphertext: BoxedUint,
  r_elliptic: <G::G as Group>::Scalar,
  delta: BoxedUint,
  x: Zeroizing<<G::G as Group>::Scalar>,
}

impl<Udk, Udp, E, G: WrappedGroup> Drop for InteractiveCiphertext<'_, Udk, Udp, E, G> {
  /// This will zeroize every secret contained within this.
  fn drop(&mut self) {
    let Self { cl15p: _, identity_p: _, generator_p: _, r_ciphertext, r_elliptic, delta, x } = self;
    r_ciphertext.zeroize();
    r_elliptic.zeroize();
    delta.zeroize();
    x.zeroize();
  }
}
impl<Udk, Udp, E, G: WrappedGroup> ZeroizeOnDrop for InteractiveCiphertext<'_, Udk, Udp, E, G> {}

impl<E: CtAssign + Element> Ciphertext<E> {
  /// Encrypt the discrete logarithm of an elliptic curve point.
  ///
  /// This function assumes the elliptic curve point has order `p` which defines the prime field
  /// `x` (the discrete logarithm) is defined over.
  ///
  /// This will write the commitment for the proof of knowledge to the transcript.
  pub(crate) fn encrypt<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, G: WrappedGroup>(
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    x: Zeroizing<<G::G as Group>::Scalar>,
    mut transcript: impl io::Write,
  ) -> io::Result<(Ciphertext<E>, InteractiveCiphertext<'_, Udk, Udp, E, G>)> {
    const STATISTICAL_DISTANCE_FROM_UNIFORM: u32 = 128;

    let delta = BoxedUint::random_bits(
      &mut rng,
      STATISTICAL_DISTANCE_FROM_UNIFORM +
        setup.cl15p().fundamental_discriminant().upper_bound_on_order(),
    );

    /*
      This is chosen such that $(r + c * x) / (c_\mathsf{prime} * p)$ is statistically uniform to
      the unknown order of the fundamental discriminant as `r / (c_\mathsf{prime} * p)` is itself
      so uniform.
    */
    let prime_bits = 8 * setup.cl15p().fundamental_discriminant().p().bits().div_ceil(8);
    let p_times_unknown_order_bound = setup.cl15p().upper_bound_on_order();
    let r_ciphertext = BoxedUint::random_bits(
      &mut rng,
      STATISTICAL_DISTANCE_FROM_UNIFORM + prime_bits + p_times_unknown_order_bound,
    );
    let r_elliptic = <G::G as Group>::Scalar::random(&mut rng);

    // TODO
    let identity_p = E::identity(setup.cl15p().absolute_value());
    let generator_p =
      Table::new(core::num::NonZero::new(6).unwrap(), E::from(setup.generator_p().clone()));

    let ciphertext = Ciphertext {
      ciphertext: Table::msm(
        &identity_p,
        &[(Zeroizing::new(delta.to_le_bytes()).as_ref(), &generator_p)],
      )
      .add(setup.cl15p().f_scaled(Zeroizing::new(crate::Up_from_scalar::<G::Up, G>(*x)).deref())),
    };

    let R_ciphertext = Table::msm(
      &identity_p,
      &[(Zeroizing::new(r_ciphertext.to_le_bytes()).as_ref(), &generator_p)],
    )
    .add(
      setup.cl15p().f_scaled(Zeroizing::new(crate::Up_from_scalar::<G::Up, G>(r_elliptic)).deref()),
    );
    let R_elliptic = G::generator_e() * r_elliptic;

    let interactive_ciphertext = InteractiveCiphertext {
      cl15p: setup.cl15p(),
      identity_p,
      generator_p,
      r_ciphertext,
      r_elliptic,
      delta,
      x,
    };

    R_ciphertext.compress(&mut transcript)?;
    transcript.write_all(R_elliptic.to_bytes().as_ref())?;

    Ok((ciphertext, interactive_ciphertext))
  }
}

impl<E: Element> Ciphertext<E> {
  /// Write the ciphertext to the transcript.
  pub(crate) fn write(self, transcript: impl io::Write) -> io::Result<()> {
    self.ciphertext.compress(transcript)
  }

  /// Read a ciphertext from the transcript.
  pub(crate) fn read<Up: BitOps, Up2, Udk: Encoding, Udp: Encoding>(
    cl15p: &Cl15p<Up, Up2, Udk, Udp>,
    transcript: impl io::Read,
  ) -> io::Result<Self> {
    Ok(Self { ciphertext: E::decompress(transcript, cl15p.absolute_value())? })
  }
}

impl<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding, E: CtAssign + Element, G: WrappedGroup>
  InteractiveCiphertext<'_, Udk, Udp, E, G>
{
  /// Respond to the challenge for the proof of knowledge.
  ///
  /// This will write the response to the transcript and return the randomness the ciphertext was
  /// encrypted with.
  pub(crate) fn respond(
    self,
    prime: &BoxedUint,
    challenge: <G::G as Group>::Scalar,
    mut transcript: impl io::Write,
  ) -> io::Result<Zeroizing<BoxedUint>> {
    // `r_ciphertext + c * delta`
    let s_delta = Zeroizing::new(self.r_ciphertext.concatenating_add(Zeroizing::new(
      crate::Up_from_scalar::<BoxedUint, G>(challenge).concatenating_mul(&self.delta),
    )));

    let divisor = NonZero::new(prime.concatenating_mul(crate::p_Up::<BoxedUint, G>()))
      .expect("the product of two primes is non-zero");
    let (d, e) = s_delta.div_rem(&divisor);
    let d = Zeroizing::new(d);

    self
      .cl15p
      .surject::<E>(Table::msm(
        &self.identity_p,
        &[(Zeroizing::new(d.to_le_bytes()).as_ref(), &self.generator_p)],
      ))
      .compress(&mut transcript)?;
    transcript.write_all(
      &e.to_le_bytes()
        [.. usize::try_from(2 * (<G::G as Group>::Scalar::NUM_BITS.div_ceil(8))).unwrap()],
    )?;
    transcript.write_all((self.r_elliptic + (challenge * self.x.deref())).to_repr().as_ref())?;

    Ok(Zeroizing::new(self.delta.clone()))
  }
}

impl<E: Element, G: WrappedGroup> Commit<E, G> {
  /// Read the commitment from the proof of knowledge from the transcript.
  pub(crate) fn read<Udk: Encoding, Udp: Encoding>(
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    mut transcript: impl io::Read,
  ) -> io::Result<Self> {
    let R_ciphertext = E::decompress(&mut transcript, setup.cl15p().absolute_value())?;
    let R_elliptic = G::point_from_canonical_bytes(&mut transcript)?;
    Ok(Self { R_ciphertext, R_elliptic })
  }

  /// Check the response (read from the transcript) to the challenge.
  ///
  /// If this errors, `batch_verifier` will be left unmodified.
  pub(crate) fn queue_batch_verification<Udk: Encoding, Udp: Encoding>(
    self,
    mut rng: impl CryptoRng,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    batch_verifier: &mut BatchVerifier<E, G>,
    ciphertext: Ciphertext<E>,
    elliptic_commitment: G::G,
    prime: &BoxedUint,
    challenge: <G::G as Group>::Scalar,
    mut transcript: impl io::Read,
  ) -> io::Result<()> {
    let Self { R_ciphertext, R_elliptic } = self;

    let D =
      E::decompress(&mut transcript, setup.cl15p().fundamental_discriminant().absolute_value())?;

    let divisor = prime.concatenating_mul(crate::p_Up::<BoxedUint, G>());
    let e = {
      let mut e = vec![0; usize::try_from(divisor.bits_precision().div_ceil(8)).unwrap()];
      transcript.read_exact(&mut e)?;
      let e = BoxedUint::from_le_bytes(e.into());
      if e >= divisor {
        Err(io::Error::other(r"$e \ge (c_\mathsf{prime} * p)$"))?;
      }
      e
    };
    let s = {
      let mut s = <<G::G as Group>::Scalar as PrimeField>::Repr::default();
      transcript.read_exact(s.as_mut())?;
      Option::<<G::G as Group>::Scalar>::from(<G::G as Group>::Scalar::from_repr(s))
        .ok_or(io::Error::other("`s` did not encode a canonical scalar"))?
    };

    /*
      `R_ciphertext + c ciphertext == prime p D + e generator_p + s H`
      `R_ciphertext + c ciphertext == setup.inject_p(prime D + e generator_k) + s H`
      `(setup.inject_p(prime D + e generator_k) + s H) - (R_ciphertext + c ciphertext) == 0`
    */
    {
      let batch_verification_weight_scalar = <G::G as Group>::Scalar::random(&mut rng);
      let batch_verification_weight =
        crate::Up_from_scalar::<BoxedUint, G>(batch_verification_weight_scalar);

      // TODO: `Table::new`
      batch_verifier.k.push((
        batch_verification_weight.concatenating_mul(prime),
        Table::new(core::num::NonZero::new(4).unwrap(), D),
      ));
      batch_verifier.generator_k = batch_verifier
        .generator_k
        .concatenating_add(batch_verification_weight.concatenating_mul(e));
      // If we unnecessarily widened `batch_verifier.generator_k`, resize it back down
      // TODO: Find a better pattern for this/ensure we do it everywhere
      batch_verifier.generator_k =
        batch_verifier.generator_k.clone().resize(batch_verifier.generator_k.bits_vartime());
      batch_verifier.f += batch_verification_weight_scalar * s;

      // TODO: `Table::new`
      batch_verifier.p.extend([
        (
          batch_verification_weight
            .concatenating_mul(crate::Up_from_scalar::<BoxedUint, G>(challenge)),
          Table::new(core::num::NonZero::new(4).unwrap(), -ciphertext.ciphertext),
        ),
        (batch_verification_weight, Table::new(core::num::NonZero::new(4).unwrap(), -R_ciphertext)),
      ]);
    }

    // `R_elliptic + c elliptic_commitment == s generator_e`
    {
      let batch_verification_weight = <G::G as Group>::Scalar::random(&mut rng);
      batch_verifier.e.push((batch_verification_weight, R_elliptic));
      batch_verifier.e.push((batch_verification_weight * challenge, elliptic_commitment));
      batch_verifier.generator_e -= batch_verification_weight * s;
    }

    Ok(())
  }
}
