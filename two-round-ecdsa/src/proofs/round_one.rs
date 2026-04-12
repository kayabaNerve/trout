use core::{marker::PhantomData, ops::Deref};
use std::io::{self, Read, Write};

use zeroize::Zeroizing;
use rand::CryptoRng;

use ::malachite::{base::num::basic::traits::*, *};

use group::{
  ff::{Field, PrimeField},
  Group, GroupEncoding,
};
use class_groups::{Element, Table, ClassGroup};

use crate::{UnsignedInteger, DigestReader, DigestWriter, Primes, Parameters};

/// The proofs for the first round.
///
/// These proofs need to prove
/// `R_{i_j} = E \cdot k_{i_j} \and K_{i_j} = (\alpha_i \cdot G + k_{i_j} \cdot H) for j \in [2]`
/// and `U_i = \beta_i \cdot G` (that `Ki` is the ciphertext of the nonce and `U_i` has a known
/// opening).
pub trait RoundOneProofs<CG: Element, P: Parameters<CG>> {
  /// The batch verifier for the round one proofs.
  type BatchVerifier;

  /// Prove the round one statements.
  ///
  /// This uses `P::E::generator()`, where `E` is the generic type parameter, for `E`, the elliptic
  /// curve generator from the academic notation. This also uses `ClassGroup::f()` for `H`.
  ///
  /// The provided transcript MUST already be binding to `E, G, H, R_i, K_i, U_i`. This
  /// allows the proofs to not transcript these.
  ///
  /// If an error is returned, the state of `transcript` is undefined.
  fn prove<W: io::Write>(
    rng: &mut impl CryptoRng,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    alpha_i: (&UnsignedInteger, &UnsignedInteger),
    k_i: (&P::F, &P::F),
    beta_i: &UnsignedInteger,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()>;

  /// Create a batch verifier of round one proofs.
  fn batch_verifier(proofs: usize) -> Self::BatchVerifier;

  /// Queue verification of someone's round one proofs.
  ///
  /// This transcript must be the exact same as the prover used, causing the same bounds on what
  /// has already been transcripted.
  ///
  /// If an error is returned, `transcript` is left in an undefined state. The batch verifier is
  /// guaranteed to not be mutated however, meaning a proof which raises an error while being
  /// queued will not corrupt the batch verifier and will leave it eligible to verify other proofs.
  fn queue_verification<R: io::Read>(
    rng: &mut impl CryptoRng,
    batch_verifier: &mut Self::BatchVerifier,
    participant: dkg::Participant,
    class_group: &ClassGroup<CG>,
    R_i: (P::E, P::E),
    K_i: (CG, CG),
    U_i: CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()>;

  /// Verify all proofs within the batch verifier.
  ///
  /// Returns `Ok(())` or a list of *all* of the *faulty* participants.
  fn verify(
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    batch_verifier: Self::BatchVerifier,
  ) -> Result<(), Vec<dkg::Participant>>;
}

/// The batch verifier for `Ccykc2023RoundOne`.
pub struct Ccykc2023RoundOneBatchVerifier<CG: Element, P: Parameters<CG>> {
  G: Natural,
  H: P::F,
  E: P::F,
  additional_elliptic_curve: Vec<(P::F, P::E)>,
  additional_class_group: Vec<(CG, Natural)>,
}

/// Proofs from Cui, Chan, Yuen, Kang, and Chu's Bandwidth-Efficient Zero-Knowledge Proofs for
/// Threshold ECDSA (2023).
pub struct Ccykc2023RoundOne<Pr: Primes>(PhantomData<Pr>);
impl<CG: Element, P: Parameters<CG>, Pr: Primes> RoundOneProofs<CG, P> for Ccykc2023RoundOne<Pr> {
  type BatchVerifier = Ccykc2023RoundOneBatchVerifier<CG, P>;

  fn prove<W: io::Write>(
    rng: &mut impl CryptoRng,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    alpha_i: (&UnsignedInteger, &UnsignedInteger),
    k_i: (&P::F, &P::F),
    beta_i: &UnsignedInteger,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()> {
    let B = crate::ccykc::B::<P::F, _>(class_group);

    // Algorithm 6 ZKPoKLog, to prove the integrity of `R_{i_j}, K_{i_j}`, yet omitting what would
    // be the commitment to the randomness for the ciphertext
    // `s_p` according to the paper
    let r_randomness_0 = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    // `s_m` according to the paper
    let r_message_0 = Zeroizing::new(P::F::random(&mut *rng));
    // Write $\hat{S}$ from the paper
    transcript.write_all((P::E::generator() * r_message_0.deref()).to_bytes().as_ref())?;
    // Write `S_1` from the paper
    CG::multiexp(
      class_group.identity_p(),
      &[
        (G, &Zeroizing::new(r_randomness_0.to_be_bytes())),
        (class_group.f(), &Zeroizing::new(crate::be_bytes(r_message_0.deref()))),
      ],
    )
    .compress(&mut *transcript)?;

    let r_randomness_1 = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    let r_message_1 = Zeroizing::new(P::F::random(&mut *rng));
    transcript.write_all((P::E::generator() * r_message_1.deref()).to_bytes().as_ref())?;
    CG::multiexp(
      class_group.identity_p(),
      &[
        (G, &Zeroizing::new(r_randomness_1.to_be_bytes())),
        (class_group.f(), &Zeroizing::new(crate::be_bytes(r_message_1.deref()))),
      ],
    )
    .compress(&mut *transcript)?;

    // Algorithm 1 ZKPoKRepS to prove the integrity of `U_i`
    // TODO: This trimmed the other generator, and is likely solely an algorithm titled ZKPoK or
    // approximate now? Update the citation for this
    // `k_0` according to the paper
    let k_beta_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    // Write `R` from the paper
    CG::mul(G, &Zeroizing::new(k_beta_i.to_be_bytes())).compress(&mut *transcript)?;

    // Sample a challenge for all proofs
    // This is done as sampling the prime is presumed expensive, so reducing samples is appreciated
    let c = P::from_xof(transcript.0.finalize_xof());
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());

    let c_uint = UnsignedInteger::from_be_slice(&crate::be_bytes(&c));
    let modulus =
      crypto_bigint::NonZero::new((&prime * &UnsignedInteger::from_be_slice(class_group.p())).0)
        .unwrap();

    // ZKPoKLog response
    for (r_randomness, r_message, alpha_i, k_i) in [
      (r_randomness_0, r_message_0, alpha_i.0, k_i.0),
      (r_randomness_1, r_message_1, alpha_i.1, k_i.1),
    ] {
      {
        // `u_m` from the paper
        let s_message = *r_message + Zeroizing::new(c * k_i).deref();
        transcript.write_all(s_message.to_repr().as_ref())?;
      }

      // `u_p` from the paper
      let s_randomness =
        Zeroizing::new(r_randomness.deref() + Zeroizing::new(&c_uint * alpha_i).deref());
      // `(d_p, e_p)` from the paper
      let (d_randomness, e_randomness) = s_randomness.div_rem(&modulus);
      // Write `D_2` from the paper
      CG::mul(G, &d_randomness).compress(&mut *transcript)?;
      // Write `e_p` from the paper
      crate::ccykc::write_e(&mut *transcript, &modulus, e_randomness)?;
    }

    // ZKPoKRepS response
    {
      // `s_0` from the paper
      let s_beta_i = Zeroizing::new(k_beta_i.deref() + Zeroizing::new(&c_uint * beta_i).deref());
      let (d_beta_i, e_beta_i) = s_beta_i.div_rem(&modulus);
      // Write `D` from the paper
      CG::mul(G, &d_beta_i).compress(&mut *transcript)?;
      // Write `e_0` from the paper
      crate::ccykc::write_e(&mut *transcript, &modulus, e_beta_i)?;
    }

    Ok(())
  }

  fn batch_verifier(proofs: usize) -> Self::BatchVerifier {
    Ccykc2023RoundOneBatchVerifier {
      G: Natural::ZERO,
      H: P::F::ZERO,
      E: P::F::ZERO,
      additional_elliptic_curve: Vec::with_capacity(2 * proofs),
      additional_class_group: Vec::with_capacity(10 * proofs),
    }
  }

  fn queue_verification<R: io::Read>(
    rng: &mut impl CryptoRng,
    batch_verifier: &mut Self::BatchVerifier,
    _participant: dkg::Participant,
    class_group: &ClassGroup<CG>,
    R_i: (P::E, P::E),
    K_i: (CG, CG),
    U_i: CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()> {
    // ZKPoKLog commitment
    let R_message_0 = P::read_canonical_E(&mut *transcript)?;
    let R_ciphertext_0 = class_group.decompress_p(&mut *transcript)?;
    let R_message_1 = P::read_canonical_E(&mut *transcript)?;
    let R_ciphertext_1 = class_group.decompress_p(&mut *transcript)?;

    // ZKPoKRepS commitment
    let R_U = class_group.decompress_p(&mut *transcript)?;

    let c = P::from_xof(transcript.0.finalize_xof());
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());
    let prime = crate::ccykc::natural_from_bytes(&prime.to_be_bytes());

    let c_uint = crate::ccykc::natural_from_bytes(&crate::be_bytes(&c));
    let modulus = crate::ccykc::natural_from_bytes(class_group.p()) * &prime;

    // ZKPoKLog response
    let mut s_message_0 = <P::F as PrimeField>::Repr::default();
    transcript.read_exact(s_message_0.as_mut())?;
    let s_message_0 = Option::<P::F>::from(P::F::from_repr(s_message_0))
      .ok_or_else(|| io::Error::other("invalid s_message"))?;

    let D_ciphertext_0 = class_group.decompress_p(&mut *transcript)?;
    let e_randomness_0 = crate::ccykc::read_e(&mut *transcript, &modulus)?;

    let mut s_message_1 = <P::F as PrimeField>::Repr::default();
    transcript.read_exact(s_message_1.as_mut())?;
    let s_message_1 = Option::<P::F>::from(P::F::from_repr(s_message_1))
      .ok_or_else(|| io::Error::other("invalid s_message"))?;

    let D_ciphertext_1 = class_group.decompress_p(&mut *transcript)?;
    let e_randomness_1 = crate::ccykc::read_e(&mut *transcript, &modulus)?;

    // ZKPoKRepS response
    let D_U = class_group.decompress_p(&mut *transcript)?;
    let e_beta_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;

    // We now start mutating the batch verifier, so it's important we don't error from here on

    // ZKPoKLog accumulation
    {
      {
        let weight = P::F::random(&mut *rng);
        batch_verifier.additional_elliptic_curve.push((weight, R_message_0));
        batch_verifier.additional_elliptic_curve.push((weight * c, R_i.0));
        batch_verifier.E -= weight * s_message_0;
      }

      {
        let weight = P::F::random(&mut *rng);
        batch_verifier.additional_elliptic_curve.push((weight, R_message_1));
        batch_verifier.additional_elliptic_curve.push((weight * c, R_i.1));
        batch_verifier.E -= weight * s_message_1;
      }

      {
        let weight_scalar = P::F::random(&mut *rng);
        let weight = crate::ccykc::natural_from_bytes(&crate::be_bytes(&weight_scalar));
        batch_verifier.additional_class_group.push((D_ciphertext_0, &weight * &modulus));
        batch_verifier.G += &weight * &e_randomness_0;
        batch_verifier.H += weight_scalar * s_message_0;

        batch_verifier.additional_class_group.push((-R_ciphertext_0, weight.clone()));
        batch_verifier.additional_class_group.push((-K_i.0, &weight * &c_uint));
      }

      {
        let weight_scalar = P::F::random(&mut *rng);
        let weight = crate::ccykc::natural_from_bytes(&crate::be_bytes(&weight_scalar));
        batch_verifier.additional_class_group.push((D_ciphertext_1, &weight * &modulus));
        batch_verifier.G += &weight * &e_randomness_1;
        batch_verifier.H += weight_scalar * s_message_1;

        batch_verifier.additional_class_group.push((-R_ciphertext_1, weight.clone()));
        batch_verifier.additional_class_group.push((-K_i.1, &weight * &c_uint));
      }
    }

    // ZKPoKRepS accumulation
    {
      let mut weight = [0; 16];
      rng.fill_bytes(&mut weight);
      let weight = crate::ccykc::natural_from_bytes(&weight);

      batch_verifier.additional_class_group.push((D_U, &weight * &modulus));
      batch_verifier.G += &weight * &e_beta_i;

      batch_verifier.additional_class_group.push((-R_U, weight.clone()));
      batch_verifier.additional_class_group.push((-U_i, &weight * &c_uint));
    }

    Ok(())
  }

  fn verify(
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    batch_verifier: Self::BatchVerifier,
  ) -> Result<(), Vec<dkg::Participant>> {
    {
      let G_scalar = crate::ccykc::natural_to_bytes(&batch_verifier.G);
      let H_scalar = crate::be_bytes(&batch_verifier.H);
      let mut additional = Vec::with_capacity(batch_verifier.additional_class_group.len());
      for (point, scalar) in batch_verifier.additional_class_group {
        let bytes = crate::ccykc::natural_to_bytes(&scalar);
        additional.push((
          Table::new_for_scalar_bits(bytes.len() * 8, class_group.identity_p().clone(), point),
          bytes,
        ));
      }
      let mut multiexp: Vec<(_, &[u8])> = Vec::with_capacity(3 + additional.len());
      multiexp.push((G, &G_scalar));
      multiexp.push((class_group.f(), &H_scalar));
      for (table, scalar) in &additional {
        multiexp.push((table, scalar));
      }
      if CG::multiexp(class_group.identity_p(), &multiexp) != *class_group.identity_p() {
        todo!("TODO");
      }
    }

    {
      let mut multiexp = batch_verifier.additional_elliptic_curve;
      multiexp.push((batch_verifier.E, P::E::generator()));
      if !bool::from(::multiexp::multiexp_vartime(&multiexp).is_identity()) {
        todo!("TODO");
      }
    }

    Ok(())
  }
}
