use alloc::{vec::Vec, vec};
use std::io;

use rand::CryptoRng;

use group::{ff::Field as _, Group};

use crypto_bigint::{CtEq, CtAssign, NonZero, Limb, Mul, Div, BitOps as _, Encoding};
use class_groups::{NegativeDiscriminant as _, Cl15p, Element, Table};

use cshake::digest::{CustomizedInit as _, Update as _, ExtendableOutput as _, XofReader as _};

use crate::{
  CopyRead, WrappedGroup, Up2, Signature, NonInteractiveSetup, BatchVerifier, Preprocess,
  PreprocessOpening, AggregatePreprocess, SigningKey, DualScaledDecryption,
};

/// The second round of the Trout++ signing protocol.
pub struct Sign;

struct Prep<E, G: WrappedGroup> {
  sponge: G::CShake,
  Delta: E,
  Alpha: E,
  neg_Beta: E,
  h_m: <G::G as Group>::Scalar,
  rho: <G::G as Group>::Scalar,
  r: <G::G as Group>::Scalar,
}

impl Sign {
  fn prep<
    Udk: Clone + AsMut<[Limb]> + Encoding,
    Udp: Encoding,
    E: Element,
    G: WrappedGroup,
    S: SigningKey<E, G>,
  >(
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    signing_key: &S,
    aggregate_preprocess: AggregatePreprocess<E, G>,
    message: impl AsRef<[u8]>,
  ) -> Prep<E, G> {
    let key_ciphertext = signing_key.ciphertext();
    let AggregatePreprocess {
      sponge: preprocess_transcript,
      nonce_commitment,
      ciphertext: nonce_ciphertext,
      commitment: Beta,
    } = aggregate_preprocess;

    let mut preprocess_context = vec![
      0;
      usize::from(
        u16::try_from((2 * u32::from(G::BITS_OF_SECURITY)).div_ceil(8))
          .expect(r"$\lceil (2 * x) / 8 \rceil \le x$")
      )
    ];
    preprocess_transcript.finalize_xof().read(&mut preprocess_context);

    let mut signing_key_context = vec![
      0;
      usize::from(
        u16::try_from((2 * u32::from(G::BITS_OF_SECURITY)).div_ceil(8))
          .expect(r"$\lceil (2 * x) / 8 \rceil \le x$")
      )
    ];
    signing_key.transcript().finalize_xof().read(&mut signing_key_context);

    let mut sponge = G::CShake::new_customized(setup.context());
    // Transcript the first round
    sponge.update(&preprocess_context);
    // Transcript the key
    sponge.update(&signing_key_context);
    // Transcript the message
    sponge.update(message.as_ref());

    let (rho, mu) = {
      let mut sponge = sponge.clone().finalize_xof();
      let rho = G::squeeze_scalar(&mut sponge);
      let mu = G::squeeze_scalar(&mut sponge);
      (rho, mu)
    };

    let nonce_commitment = (nonce_commitment * rho) + (G::generator_e() * mu);
    let r = G::x_coordinate(&nonce_commitment);
    let h_m = G::hash_message(message);

    let Delta = key_ciphertext.add(
      setup.cl15p().f_scaled(&crate::Up_from_scalar::<G::Up, G>(&(h_m * r.invert().unwrap()))),
    );
    let Alpha =
      nonce_ciphertext.ciphertext.add(
        setup.cl15p().f_scaled(&crate::Up_from_scalar::<G::Up, G>(&(mu * rho.invert().unwrap()))),
      );

    Prep { sponge, Delta, Alpha, neg_Beta: -Beta.commitment, h_m, rho, r }
  }
}

/// The Trout++ signing protocol being completed, without identifiable aborts.
// TODO: Support third-party completions
pub struct CompletingWithoutIdentifiableAborts<'a, Udk, Udp, E, G: WrappedGroup> {
  cl15p: &'a Cl15p<G::Up, Up2<G>, Udk, Udp>,
  key: G::G,
  h_m: <G::G as Group>::Scalar,
  rho: <G::G as Group>::Scalar,
  r: <G::G as Group>::Scalar,
  S_delta_beta: E,
  S_alpha_beta: E,
}

/// The Trout++ signing protocol being completed.
// TODO: Support third-party completions
pub struct Completing<'a, Udk, Udp, E, G: WrappedGroup, S, Id> {
  setup: &'a NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
  completing: CompletingWithoutIdentifiableAborts<'a, Udk, Udp, E, G>,
  signing_key: &'a S,
  Delta: Table<E>,
  Alpha: Table<E>,
  neg_Beta: Table<E>,
  sponge: G::CShake,
  batch_verifiers: Vec<(Id, BatchVerifier<E, G>)>,
}

impl Sign {
  /// Participate in the second round of Trout++ _without_ identifiable aborts.
  // TODO: Don't assume one preprocess to one key
  #[expect(clippy::needless_pass_by_value)] // A `PreprocessOpening` is single-use
  pub fn sign_without_identifiable_aborts<
    'cl15p,
    Udk: Clone + AsMut<[Limb]> + Encoding,
    Udp: Encoding,
    E: CtAssign + Element,
    VerifierElement: Element,
    G: WrappedGroup,
    S: SigningKey<VerifierElement, G>,
  >(
    setup: &'cl15p NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    signing_key: &S,
    interpolation_factor: <G::G as Group>::Scalar,
    setup_opening: S::Opening,
    aggregate_preprocess: AggregatePreprocess<VerifierElement, G>,
    preprocess_opening: PreprocessOpening,
    message: impl AsRef<[u8]>,
    mut out: impl io::Write,
  ) -> io::Result<CompletingWithoutIdentifiableAborts<'cl15p, Udk, Udp, VerifierElement, G>> {
    let Prep { sponge: _, Delta, Alpha, neg_Beta, h_m, rho, r } =
      Self::prep(setup, signing_key, aggregate_preprocess, message);
    let Delta = E::from(Delta);
    let Alpha = E::from(Alpha);
    let neg_Beta = NonInteractiveSetup::inject_p::<E>(setup.cl15p(), neg_Beta);

    // TODO: `Table::new`
    let Delta = Table::new(core::num::NonZero::new(4).unwrap(), Delta);
    let Alpha = Table::new(core::num::NonZero::new(4).unwrap(), Alpha);
    let neg_Beta = Table::new(core::num::NonZero::new(4).unwrap(), neg_Beta);

    let nonce_ciphertext_opening = &preprocess_opening.ciphertext_opening;
    let commitment_opening = &preprocess_opening.commitment_opening;

    let (S_delta_beta, S_alpha_beta) = DualScaledDecryption::<G::Up, Up2<G>, Udk, Udp, E>::decrypt(
      setup.cl15p(),
      &Delta,
      &Alpha,
      &neg_Beta,
      &signing_key.share_opening(interpolation_factor, setup_opening),
      nonce_ciphertext_opening,
      commitment_opening,
    );
    S_delta_beta.clone().compress(&mut out)?;
    S_alpha_beta.clone().compress(&mut out)?;
    Ok(CompletingWithoutIdentifiableAborts {
      cl15p: setup.cl15p(),
      key: signing_key.key(),
      h_m,
      rho,
      r,
      S_delta_beta: VerifierElement::from(S_delta_beta),
      S_alpha_beta: VerifierElement::from(S_alpha_beta),
    })
  }

  /// Participate in the second round of Trout++.
  // TODO: Don't assume one preprocess to one key
  #[expect(clippy::needless_pass_by_value)] // A `PreprocessOpening` is single-use
  pub fn sign<
    'cl15p,
    Udk: Clone + AsMut<[Limb]> + Encoding,
    Udp: Encoding,
    E: CtAssign + Element,
    VerifierElement: Element,
    PreprocessElement: Element,
    G: WrappedGroup,
    S: SigningKey<VerifierElement, G>,
    Id,
  >(
    mut rng: impl CryptoRng,
    setup: &'cl15p NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
    signing_key: &'cl15p S,
    interpolation_factor: <G::G as Group>::Scalar,
    key_share_ciphertext: S::Setup,
    setup_opening: S::Opening,
    aggregate_preprocess: AggregatePreprocess<VerifierElement, G>,
    preprocess: &Preprocess<PreprocessElement>,
    preprocess_opening: PreprocessOpening,
    message: impl AsRef<[u8]>,
    mut out: impl io::Write,
  ) -> io::Result<Completing<'cl15p, Udk, Udp, VerifierElement, G, S, Id>> {
    let Prep { sponge, Delta, Alpha, neg_Beta, h_m, rho, r } =
      Self::prep(setup, signing_key, aggregate_preprocess, message);
    let Delta = E::from(Delta);
    let Alpha = E::from(Alpha);
    let neg_Beta = NonInteractiveSetup::inject_p::<E>(setup.cl15p(), neg_Beta);
    let nonce_ciphertext_opening = preprocess_opening.ciphertext_opening.clone();
    let commitment_opening = preprocess_opening.commitment_opening.clone();

    let mut transcript = vec![];
    let (S_delta_beta, S_alpha_beta) = {
      // TODO: `Table::new`
      let Delta = Table::new(core::num::NonZero::new(4).unwrap(), Delta.clone());
      let Alpha = Table::new(core::num::NonZero::new(4).unwrap(), Alpha.clone());
      let neg_Beta = Table::new(core::num::NonZero::new(4).unwrap(), neg_Beta.clone());

      let ((S_delta_beta, S_alpha_beta), interactive_decryption) =
        DualScaledDecryption::<G::Up, Up2<G>, Udk, Udp, E>::provably_decrypt::<G>(
          &mut rng,
          setup,
          &Delta,
          &Alpha,
          &neg_Beta,
          signing_key.share_opening(interpolation_factor, setup_opening),
          nonce_ciphertext_opening,
          commitment_opening,
          &mut transcript,
        )?;

      {
        let S_delta_beta = {
          let mut bytes = vec![];
          S_delta_beta.clone().compress(&mut bytes)?;
          bytes
        };
        let S_alpha_beta = {
          let mut bytes = vec![];
          S_alpha_beta.clone().compress(&mut bytes)?;
          bytes
        };

        let mut sponge = sponge.clone();

        // Transcript this specific participant's key share's ciphertext
        sponge.update(&{
          let mut bytes = vec![];
          signing_key
            .share_ciphertext(interpolation_factor, key_share_ciphertext)
            .compress(&mut bytes)?;
          bytes
        });
        // Transcript this specific participant's preprocess
        sponge.update(&preprocess.message);
        // Transcript the second round's message
        sponge.update(&S_delta_beta);
        sponge.update(&S_alpha_beta);
        // Transcript the proof's transcript thus far
        sponge.update(&transcript);

        let (prime, challenge) = {
          let mut sponge = sponge.finalize_xof();
          crate::challenge::<G>(&mut rng, &mut sponge)
        };
        let () = interactive_decryption.respond::<G>(&prime, challenge, &mut transcript)?;

        out.write_all(&S_delta_beta)?;
        out.write_all(&S_alpha_beta)?;
        out.write_all(&transcript)?;
      }

      (S_delta_beta, S_alpha_beta)
    };

    Ok(Completing {
      setup,
      completing: CompletingWithoutIdentifiableAborts {
        cl15p: setup.cl15p(),
        key: signing_key.key(),
        h_m,
        rho,
        r,
        S_delta_beta: VerifierElement::from(S_delta_beta),
        S_alpha_beta: VerifierElement::from(S_alpha_beta),
      },
      signing_key,
      Delta: Table::new(core::num::NonZero::new(4).unwrap(), VerifierElement::from(Delta)),
      Alpha: Table::new(core::num::NonZero::new(4).unwrap(), VerifierElement::from(Alpha)),
      neg_Beta: Table::new(core::num::NonZero::new(4).unwrap(), VerifierElement::from(neg_Beta)),
      sponge,
      batch_verifiers: vec![],
    })
  }
}

impl<Udk: Encoding, Udp: Encoding, E: Element, G: WrappedGroup>
  CompletingWithoutIdentifiableAborts<'_, Udk, Udp, E, G>
{
  /// Aggregate a share from the second round of the Trout++ signing protocol, without identifiable
  /// aborts.
  pub fn aggregate(&mut self, mut read: impl io::Read) -> io::Result<()> {
    let S_delta_beta = E::decompress(&mut read, self.cl15p.absolute_value())?;
    let S_alpha_beta = E::decompress(&mut read, self.cl15p.absolute_value())?;
    self.S_delta_beta = self.S_delta_beta.clone().add(S_delta_beta);
    self.S_alpha_beta = self.S_alpha_beta.clone().add(S_alpha_beta);
    Ok(())
  }
}

impl<Udk: Encoding, Udp: Encoding, E: Element, G: WrappedGroup, S: SigningKey<E, G>, Id>
  Completing<'_, Udk, Udp, E, G, S, Id>
{
  /// Aggregate a share from the second round of the Trout++ signing protocol.
  pub fn aggregate(
    &mut self,
    mut rng: impl CryptoRng,
    id: Id,
    interpolation_factor: <G::G as Group>::Scalar,
    key_share_ciphertext: S::Setup,
    preprocess: Preprocess<E>,
    read: impl io::Read,
  ) -> io::Result<()> {
    let mut read = CopyRead { read, copy_to: vec![] };

    let S_delta_beta = E::decompress(&mut read, self.setup.cl15p().absolute_value())?;
    let S_alpha_beta = E::decompress(&mut read, self.setup.cl15p().absolute_value())?;

    let mut sponge = self.sponge.clone();
    let share_ciphertext =
      self.signing_key.share_ciphertext(interpolation_factor, key_share_ciphertext);
    sponge.update(&{
      let mut bytes = vec![];
      share_ciphertext.clone().compress(&mut bytes)?;
      bytes
    });
    sponge.update(&preprocess.message);

    let commit = crate::dual_scaled_decryption::Commit::<E>::read::<G::Up, Up2<G>, Udk, Udp>(
      self.setup.cl15p(),
      &mut read,
    )?;
    sponge.update(&read.copy_to);

    let (prime, challenge) = {
      let mut sponge = sponge.finalize_xof();
      crate::challenge::<G>(&mut rng, &mut sponge)
    };

    let mut batch_verifier = BatchVerifier::new();
    commit.queue_batch_verification(
      rng,
      self.setup.cl15p(),
      &mut batch_verifier,
      &self.Delta,
      &self.Alpha,
      &self.neg_Beta,
      share_ciphertext,
      preprocess.ciphertext.ciphertext,
      preprocess.commitment.commitment,
      S_delta_beta.clone(),
      S_alpha_beta.clone(),
      &prime,
      challenge,
      &mut read,
    )?;

    self.completing.S_delta_beta = self.completing.S_delta_beta.clone().add(S_delta_beta);
    self.completing.S_alpha_beta = self.completing.S_alpha_beta.clone().add(S_alpha_beta);
    self.batch_verifiers.push((id, batch_verifier));

    Ok(())
  }
}

impl<
  Udk,
  Udp: Clone
    + CtEq
    + for<'a> Mul<&'a G::Up, Output = Udp>
    + for<'a> Div<&'a NonZero<G::Up>, Output = Udp>
    + Encoding,
  E: Element,
  G: WrappedGroup,
> CompletingWithoutIdentifiableAborts<'_, Udk, Udp, E, G>
{
  /// Complete execution of the Trout++ signing protocol.
  ///
  /// This requires first aggregating shares from all those who have preprocessed _and_ from a
  /// collection of key shares which interpolate to the signing key.
  ///
  /// This will return `None` if either shares were improperly aggregated _or_ any shares were
  /// invalid.
  pub fn complete(self) -> Option<Signature<G>> {
    let Up_to_scalar = |up: G::Up| {
      let mut result = <G::G as Group>::Scalar::ZERO;
      for i in (0 .. up.bits_precision()).rev() {
        result = result + result;
        if up.bit_vartime(i) {
          result += <G::G as Group>::Scalar::ONE;
        }
      }
      result
    };

    let numerator =
      Up_to_scalar(Option::<G::Up>::from(self.cl15p.discrete_logarithm(self.S_delta_beta))?) *
        self.r;
    let denominator =
      Up_to_scalar(Option::<G::Up>::from(self.cl15p.discrete_logarithm(self.S_alpha_beta))?) *
        self.rho;
    let mut s = numerator * Option::<<G::G as Group>::Scalar>::from(denominator.invert())?;

    // Normalize this to have a low `s`
    if crate::Up_from_scalar::<G::Up, G>(&-s) < crate::Up_from_scalar::<G::Up, G>(&s) {
      s = -s;
    }

    if bool::from(self.r.is_zero() | s.is_zero()) {
      None?;
    }
    let R = ((G::generator_e() * self.h_m) + (self.key * self.r)) * s.invert().unwrap();
    if G::x_coordinate(&R) != self.r {
      None?;
    }

    Some(Signature { r: self.r, s })
  }
}

impl<
  Udk: Clone + AsMut<[Limb]> + Encoding,
  Udp: Clone
    + CtEq
    + for<'a> Mul<&'a G::Up, Output = Udp>
    + for<'a> Div<&'a NonZero<G::Up>, Output = Udp>
    + Encoding,
  E: Element,
  G: WrappedGroup,
  S: SigningKey<E, G>,
  Id,
> Completing<'_, Udk, Udp, E, G, S, Id>
{
  /// Complete execution of the Trout++ signing protocol.
  ///
  /// This requires first aggregating shares from all those who have preprocessed _and_ from a
  /// collection of key shares which interpolate to the signing key.
  ///
  /// This will return `Err(_)` if either shares were improperly aggregated _or_ any shares were
  /// invalid. It will then proceed to identify any invalid shares, returning the list of invalid
  /// shares' IDs as the error.
  pub fn complete(self) -> Result<Signature<G>, Vec<Id>> {
    let Self {
      setup,
      completing,
      signing_key: _,
      Delta: _,
      Alpha: _,
      neg_Beta: _,
      sponge: _,
      batch_verifiers,
    } = self;
    if let Some(signature) = completing.complete() {
      return Ok(signature);
    }

    let mut result = vec![];
    for (id, batch_verifier) in batch_verifiers {
      if matches!(batch_verifier.verify(setup), Ok(())) {
        continue;
      }
      result.push(id);
    }
    Err(result)
  }
}
