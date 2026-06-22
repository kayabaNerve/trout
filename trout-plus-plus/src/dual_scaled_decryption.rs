use alloc::vec;
use std::io;

use zeroize::{Zeroize as _, ZeroizeOnDrop, Zeroizing};
use rand::CryptoRng;

use group::{ff::PrimeField as _, Group};

use crypto_bigint::{
  CtAssign, Zero, NonZero, Limb, ConcatenatingMul as _, ConcatenatingSquare, BitOps, Encoding,
  RandomBits as _, BoxedUint,
};
use class_groups::{NegativeDiscriminant as _, FundamentalDiscriminant as _, Element, Cl15p, Table};

use crate::{WrappedGroup, NonInteractiveSetup, BatchVerifier};

/// The commitment for the proof of correctness.
pub(crate) struct Commit<E> {
  R_delta: E,
  R_alpha: E,
  R_beta: E,
  R_delta_beta: E,
  R_alpha_beta: E,
}

pub(crate) struct DualScaledDecryption<'a, Up, Up2, Udk, Udp, E> {
  cl15p: &'a Cl15p<Up, Up2, Udk, Udp>,
  identity_k: E,
  identity_p: E,
  generator_k: Table<E>,
  p_generator_k: Table<E>,
  Delta: &'a Table<E>,
  Alpha: &'a Table<E>,
  neg_Beta: &'a Table<E>,
  r_delta: BoxedUint,
  r_alpha: BoxedUint,
  r_beta: BoxedUint,
  delta_i: Zeroizing<BoxedUint>,
  alpha_i: Zeroizing<BoxedUint>,
  beta_i: Zeroizing<BoxedUint>,
}

impl<Up, Up2, Udk, Udp, E> Drop for DualScaledDecryption<'_, Up, Up2, Udk, Udp, E> {
  /// This will zeroize every secret contained within this.
  fn drop(&mut self) {
    let Self {
      cl15p: _,
      identity_k: _,
      identity_p: _,
      generator_k: _,
      p_generator_k: _,
      Delta: _,
      Alpha: _,
      neg_Beta: _,
      r_delta,
      r_alpha,
      r_beta,
      delta_i,
      alpha_i,
      beta_i,
    } = self;
    r_delta.zeroize();
    r_alpha.zeroize();
    r_beta.zeroize();
    delta_i.zeroize();
    alpha_i.zeroize();
    beta_i.zeroize();
  }
}
impl<Up, Up2, Udk, Udp, E> ZeroizeOnDrop for DualScaledDecryption<'_, Up, Up2, Udk, Udp, E> {}

impl<'a, Up: BitOps, Up2, Udk: Encoding, Udp: Encoding, E: CtAssign + Element>
  DualScaledDecryption<'a, Up, Up2, Udk, Udp, E>
{
  /// Perform two invocations of the scaled decryption protocol against two ciphertexts with the
  /// same commitment.
  pub(crate) fn decrypt(
    cl15p: &'a Cl15p<Up, Up2, Udk, Udp>,
    Delta: &'a Table<E>,
    Alpha: &'a Table<E>,
    neg_Beta: &'a Table<E>,
    delta_i: &Zeroizing<BoxedUint>,
    alpha_i: &Zeroizing<BoxedUint>,
    beta_i: &Zeroizing<BoxedUint>,
  ) -> (E, E) {
    // TODO
    let identity_p = E::identity(cl15p.absolute_value());

    let beta_i = Zeroizing::new(beta_i.to_le_bytes());
    let S_delta_beta = Table::msm(
      &identity_p,
      &[(Zeroizing::new(delta_i.to_le_bytes()).as_ref(), neg_Beta), (beta_i.as_ref(), Delta)],
    );
    let S_alpha_beta = Table::msm(
      &identity_p,
      &[(Zeroizing::new(alpha_i.to_le_bytes()).as_ref(), neg_Beta), (beta_i.as_ref(), Alpha)],
    );
    (S_delta_beta, S_alpha_beta)
  }

  /// Perform two invocations of the scaled decryption protocol against two ciphertexts with the
  /// same commitment, beginning an interactive proof of correctness.
  pub(crate) fn provably_decrypt<G: WrappedGroup<Up = Up>>(
    mut rng: impl CryptoRng,
    setup: &'a NonInteractiveSetup<Up, Up2, Udk, Udp>,
    Delta: &'a Table<E>,
    Alpha: &'a Table<E>,
    neg_Beta: &'a Table<E>,
    delta_i: Zeroizing<BoxedUint>,
    alpha_i: Zeroizing<BoxedUint>,
    beta_i: Zeroizing<BoxedUint>,
    mut transcript: impl io::Write,
  ) -> io::Result<((E, E), DualScaledDecryption<'a, Up, Up2, Udk, Udp, E>)> {
    let cl15p = setup.cl15p();

    let (S_delta_beta, S_alpha_beta) =
      Self::decrypt(cl15p, Delta, Alpha, neg_Beta, &delta_i, &alpha_i, &beta_i);

    const STATISTICAL_DISTANCE_FROM_UNIFORM: u32 = 128;

    let prime_bits = 8 * cl15p.fundamental_discriminant().p().bits().div_ceil(8);
    let p_times_unknown_order_bound = cl15p.upper_bound_on_order();
    let r_delta = BoxedUint::random_bits(
      &mut rng,
      STATISTICAL_DISTANCE_FROM_UNIFORM +
        prime_bits +
        <G::G as Group>::Scalar::NUM_BITS +
        p_times_unknown_order_bound,
    );
    let r_alpha = BoxedUint::random_bits(
      &mut rng,
      STATISTICAL_DISTANCE_FROM_UNIFORM +
        prime_bits +
        <G::G as Group>::Scalar::NUM_BITS +
        p_times_unknown_order_bound,
    );
    let r_beta = BoxedUint::random_bits(
      &mut rng,
      STATISTICAL_DISTANCE_FROM_UNIFORM + prime_bits + p_times_unknown_order_bound,
    );

    // TODO
    let identity_k = E::identity(cl15p.fundamental_discriminant().absolute_value());
    let identity_p = E::identity(cl15p.absolute_value());
    let generator_k =
      Table::new(core::num::NonZero::new(4).unwrap(), E::from(setup.generator_k().clone()));
    let p_generator_k = Table::new(
      core::num::NonZero::new(4).unwrap(),
      Table::msm_vartime(
        identity_k.clone(),
        &[(crate::p_Up::<BoxedUint, G>().to_le_bytes().as_ref(), &generator_k)],
      ),
    );

    let (R_delta, R_alpha, R_beta, R_delta_beta, R_alpha_beta) = {
      let r_delta = Zeroizing::new(r_delta.to_le_bytes());
      let r_alpha = Zeroizing::new(r_alpha.to_le_bytes());
      let r_beta = Zeroizing::new(r_beta.to_le_bytes());
      let R_delta = Table::msm(&identity_k, &[(r_delta.as_ref(), &p_generator_k)]);
      let R_alpha = Table::msm(&identity_k, &[(r_alpha.as_ref(), &p_generator_k)]);
      let R_beta = Table::msm(&identity_k, &[(r_beta.as_ref(), &generator_k)]);
      let R_delta_beta =
        Table::msm(&identity_p, &[(r_delta.as_ref(), neg_Beta), (r_beta.as_ref(), Delta)]);
      let R_alpha_beta =
        Table::msm(&identity_p, &[(r_alpha.as_ref(), neg_Beta), (r_beta.as_ref(), Alpha)]);
      (R_delta, R_alpha, R_beta, R_delta_beta, R_alpha_beta)
    };

    let scaled_decryption = DualScaledDecryption {
      cl15p,
      identity_k,
      identity_p,
      generator_k,
      p_generator_k,
      Delta,
      Alpha,
      neg_Beta,
      r_delta,
      r_alpha,
      r_beta,
      delta_i,
      alpha_i,
      beta_i,
    };

    R_delta.compress(&mut transcript)?;
    R_alpha.compress(&mut transcript)?;
    R_beta.compress(&mut transcript)?;
    R_delta_beta.compress(&mut transcript)?;
    R_alpha_beta.compress(&mut transcript)?;

    Ok(((S_delta_beta, S_alpha_beta), scaled_decryption))
  }
}

impl<
  Up: AsRef<[Limb]> + Zero + ConcatenatingSquare + BitOps + Encoding,
  Up2,
  Udk: Clone + AsMut<[Limb]> + Encoding,
  Udp: Encoding,
  E: CtAssign + Element,
> DualScaledDecryption<'_, Up, Up2, Udk, Udp, E>
{
  /// Respond to the challenge for the proof of correctness.
  ///
  /// This will write the response to the transcript.
  pub(crate) fn respond<G: WrappedGroup<Up = Up>>(
    self,
    prime: &BoxedUint,
    challenge: <G::G as Group>::Scalar,
    mut transcript: impl io::Write,
  ) -> io::Result<()> {
    let challenge_Up = crate::Up_from_scalar::<BoxedUint, G>(&challenge);

    let s_delta = Zeroizing::new(
      self.r_delta.concatenating_add(Zeroizing::new(challenge_Up.concatenating_mul(&self.delta_i))),
    );
    let s_alpha = Zeroizing::new(
      self.r_alpha.concatenating_add(Zeroizing::new(challenge_Up.concatenating_mul(&self.alpha_i))),
    );
    let s_beta = Zeroizing::new(
      self.r_beta.concatenating_add(Zeroizing::new(challenge_Up.concatenating_mul(&self.beta_i))),
    );

    let p = crate::p_Up::<BoxedUint, G>();
    let divisor =
      NonZero::new(prime.concatenating_mul(&p)).expect("the product of two primes is non-zero");
    let (d_delta, e_delta) = s_delta.div_rem(&divisor);
    let d_delta = Zeroizing::new(d_delta);
    let (d_alpha, e_alpha) = s_alpha.div_rem(&divisor);
    let d_alpha = Zeroizing::new(d_alpha);
    let (d_beta, e_beta) = s_beta.div_rem(&divisor);
    let d_beta = Zeroizing::new(d_beta);

    let (D_delta, D_alpha, D_beta, D_delta_beta, D_alpha_beta) = {
      let d_beta = Zeroizing::new(d_beta.to_le_bytes());

      let D_delta = Table::msm(
        &self.identity_k,
        &[(
          Zeroizing::new(d_delta.concatenating_mul(&p).to_le_bytes()).as_ref(),
          &self.p_generator_k,
        )],
      );
      let D_alpha = Table::msm(
        &self.identity_k,
        &[(
          Zeroizing::new(d_alpha.concatenating_mul(&p).to_le_bytes()).as_ref(),
          &self.p_generator_k,
        )],
      );
      let D_beta = Table::msm(&self.identity_k, &[(d_beta.as_ref(), &self.generator_k)]);
      let D_delta_beta = Table::msm(
        &self.identity_p,
        &[
          (Zeroizing::new(d_delta.to_le_bytes()).as_ref(), self.neg_Beta),
          (d_beta.as_ref(), self.Delta),
        ],
      );
      let D_alpha_beta = Table::msm(
        &self.identity_p,
        &[
          (Zeroizing::new(d_alpha.to_le_bytes()).as_ref(), self.neg_Beta),
          (d_beta.as_ref(), self.Alpha),
        ],
      );

      (D_delta, D_alpha, D_beta, D_delta_beta, D_alpha_beta)
    };

    D_delta.compress(&mut transcript)?;
    D_alpha.compress(&mut transcript)?;
    D_beta.compress(&mut transcript)?;
    self.cl15p.surject::<E>(D_delta_beta).compress(&mut transcript)?;
    self.cl15p.surject::<E>(D_alpha_beta).compress(&mut transcript)?;
    transcript.write_all(
      &e_delta.to_le_bytes()
        [.. usize::try_from(2 * (<G::G as Group>::Scalar::NUM_BITS.div_ceil(8))).unwrap()],
    )?;
    transcript.write_all(
      &e_alpha.to_le_bytes()
        [.. usize::try_from(2 * (<G::G as Group>::Scalar::NUM_BITS.div_ceil(8))).unwrap()],
    )?;
    transcript.write_all(
      &e_beta.to_le_bytes()
        [.. usize::try_from(2 * (<G::G as Group>::Scalar::NUM_BITS.div_ceil(8))).unwrap()],
    )?;

    Ok(())
  }
}

impl<E: Element> Commit<E> {
  /// Read the commitment from the proof of correctness from the transcript.
  pub(crate) fn read<Up: BitOps, Up2, Udk: Encoding, Udp: Encoding>(
    cl15p: &Cl15p<Up, Up2, Udk, Udp>,
    mut transcript: impl io::Read,
  ) -> io::Result<Self> {
    let R_delta =
      E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;
    let R_alpha =
      E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;
    let R_beta = E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;
    let R_delta_beta = E::decompress(&mut transcript, cl15p.absolute_value())?;
    let R_alpha_beta = E::decompress(&mut transcript, cl15p.absolute_value())?;
    Ok(Self { R_delta, R_alpha, R_beta, R_delta_beta, R_alpha_beta })
  }

  /// Check the response (read from the transcript) to the challenge.
  pub(crate) fn queue_batch_verification<
    Up: AsRef<[Limb]> + Zero + ConcatenatingSquare + BitOps + Encoding,
    Up2,
    Udk: Encoding,
    Udp: Encoding,
    G: WrappedGroup<Up = Up>,
  >(
    self,
    mut rng: impl CryptoRng,
    cl15p: &Cl15p<Up, Up2, Udk, Udp>,
    batch_verifier: &mut BatchVerifier<E, G>,
    Delta: &Table<E>,
    Alpha: &Table<E>,
    neg_Beta: &Table<E>,
    Delta_i: E,
    Alpha_i: E,
    Beta_i: E,
    S_delta_beta_i: E,
    S_alpha_beta_i: E,
    prime: &BoxedUint,
    challenge: <G::G as Group>::Scalar,
    mut transcript: impl io::Read,
  ) -> io::Result<()> {
    let Self { R_delta, R_alpha, R_beta, R_delta_beta, R_alpha_beta } = self;

    let p = NonZero::new(BoxedUint::from(<_ as AsRef<[Limb]>>::as_ref(
      cl15p.fundamental_discriminant().p().as_ref(),
    )))
    .unwrap();
    let R_delta = cl15p.fundamental_discriminant().inject::<_, BoxedUint, E>(R_delta, &p);
    let R_alpha = cl15p.fundamental_discriminant().inject::<_, BoxedUint, E>(R_alpha, &p);

    let D_delta =
      E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;
    let D_delta = cl15p.fundamental_discriminant().inject::<_, BoxedUint, _>(D_delta, &p);

    let D_alpha =
      E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;
    let D_alpha = cl15p.fundamental_discriminant().inject::<_, BoxedUint, _>(D_alpha, &p);

    let D_beta = E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;

    let D_delta_beta =
      E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;
    let D_delta_beta = cl15p.fundamental_discriminant().inject::<_, BoxedUint, _>(D_delta_beta, &p);

    let D_alpha_beta =
      E::decompress(&mut transcript, cl15p.fundamental_discriminant().absolute_value())?;
    let D_alpha_beta = cl15p.fundamental_discriminant().inject::<_, BoxedUint, _>(D_alpha_beta, &p);

    let p = crate::p_Up::<BoxedUint, G>();
    let divisor = prime.concatenating_mul(&p);
    let mut read_e = || {
      let mut e = vec![0; usize::try_from(divisor.bits_precision().div_ceil(8)).unwrap()];
      transcript.read_exact(&mut e)?;
      let e = BoxedUint::from_le_bytes(e.into());
      if e >= divisor {
        return Err(io::Error::other(r"$e \ge (c_\mathsf{prime} * p)$"));
      }
      Ok(e)
    };
    let e_delta = read_e()?;
    let e_alpha = read_e()?;
    let e_beta = read_e()?;

    let challenge = crate::Up_from_scalar::<BoxedUint, G>(&challenge);

    // TODO
    let table_bits = core::num::NonZero::new(4).unwrap();
    {
      let batch_verification_weight = BoxedUint::random_bits(&mut rng, 128);
      let batch_verification_weight = batch_verification_weight.concatenating_mul(&p);
      batch_verifier.generator_p = batch_verifier
        .generator_p
        .concatenating_add(batch_verification_weight.concatenating_mul(&e_delta));
      batch_verifier.p.extend([
        (batch_verification_weight.concatenating_mul(prime), Table::new(table_bits, D_delta)),
        (batch_verification_weight.concatenating_mul(&challenge), Table::new(table_bits, -Delta_i)),
        (batch_verification_weight, Table::new(table_bits, -R_delta)),
      ]);
    }
    {
      let batch_verification_weight = BoxedUint::random_bits(&mut rng, 128);
      let batch_verification_weight = batch_verification_weight.concatenating_mul(&p);
      batch_verifier.generator_p = batch_verifier
        .generator_p
        .concatenating_add(batch_verification_weight.concatenating_mul(&e_alpha));
      batch_verifier.p.extend([
        (batch_verification_weight.concatenating_mul(prime), Table::new(table_bits, D_alpha)),
        (batch_verification_weight.concatenating_mul(&challenge), Table::new(table_bits, -Alpha_i)),
        (batch_verification_weight, Table::new(table_bits, -R_alpha)),
      ]);
    }
    {
      let batch_verification_weight = BoxedUint::random_bits(&mut rng, 128);
      batch_verifier.generator_k = batch_verifier
        .generator_k
        .concatenating_add(batch_verification_weight.concatenating_mul(&e_beta));
      batch_verifier.k.extend([
        (batch_verification_weight.concatenating_mul(&divisor), Table::new(table_bits, D_beta)),
        (batch_verification_weight.concatenating_mul(&challenge), Table::new(table_bits, -Beta_i)),
        (batch_verification_weight, Table::new(table_bits, -R_beta)),
      ]);
    }
    {
      let batch_verification_weight = BoxedUint::random_bits(&mut rng, 128);
      batch_verifier.p.extend([
        (
          batch_verification_weight.concatenating_mul(&challenge),
          Table::new(table_bits, -S_delta_beta_i),
        ),
        (
          batch_verification_weight.concatenating_mul(&divisor),
          Table::new(table_bits, D_delta_beta),
        ),
        (batch_verification_weight.concatenating_mul(&e_beta), Delta.clone()),
        (batch_verification_weight.concatenating_mul(&e_delta), neg_Beta.clone()),
        (batch_verification_weight, Table::new(table_bits, -R_delta_beta)),
      ]);
    }
    {
      let batch_verification_weight = BoxedUint::random_bits(&mut rng, 128);
      batch_verifier.p.extend([
        (
          batch_verification_weight.concatenating_mul(&challenge),
          Table::new(table_bits, -S_alpha_beta_i),
        ),
        (
          batch_verification_weight.concatenating_mul(&divisor),
          Table::new(table_bits, D_alpha_beta),
        ),
        (batch_verification_weight.concatenating_mul(&e_beta), Alpha.clone()),
        (batch_verification_weight.concatenating_mul(&e_alpha), neg_Beta.clone()),
        (batch_verification_weight, Table::new(table_bits, -R_alpha_beta)),
      ]);
    }

    Ok(())
  }
}
