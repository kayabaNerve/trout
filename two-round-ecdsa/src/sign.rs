use core::{marker::PhantomData, ops::Deref as _};
use alloc::sync::Arc;
use std::{
  collections::{HashSet, HashMap},
  io::Write as _,
};

use zeroize::Zeroizing;
use rand::CryptoRng;

use group::{
  ff::{Field as _, PrimeField as _, PrimeFieldBits},
  Group as _, GroupEncoding as _,
};
use class_groups::{ElementExt, Table, ClassGroup};

use dkg::Participant;

use crate::{
  UnsignedInteger, DigestReader, DigestWriter, RoundOneProofs as _, RoundTwoProofs as _,
  Parameters, SetupView, Setup,
};

/// Table a ciphertext for scaled decryption.
///
/// This just yields the presumably-optimal table sizes.
fn table_scaled_decryption_ciphertext<
  PCG: ElementExt,
  CG: ElementExt,
  P: Parameters<PCG> + Parameters<CG>,
>(
  class_group: &ClassGroup<PCG>,
  ciphertext: CG,
) -> Table<PCG> {
  let ciphertext = PCG::from(ciphertext);

  Table::new_for_scalar_bits(
    // The protocol scales by an elliptic curve scalar yet the proofs presumably scale by a
    // uniform-to-the-class-group scalar
    usize::try_from(<P as Parameters<PCG>>::F::NUM_BITS).unwrap() +
      usize::try_from(class_group.unknown_order_bound() + 128).unwrap(),
    class_group.identity_p(),
    ciphertext,
  )
}

/// The 2-round signing protocol.
pub struct SigningProtocol<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>>(
  PhantomData<(PCG, CG, P)>,
);

/// A view of someone observing the signing protocol.
pub struct Observing<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<SetupView<PCG, CG, P>>,
  transcript: blake3::Hasher,
  accumulated: HashMap<
    Participant,
    (blake3::Hasher, (<P as Parameters<PCG>>::E, <P as Parameters<PCG>>::E), (CG, CG), CG),
  >,
  faulty: HashSet<Participant>,
  pending: HashMap<Participant, Vec<u8>>,
}

/// A view of someone participating in the signing protocol.
pub struct Participating<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<Setup<PCG, CG, P>>,
  alpha_i: (Zeroizing<UnsignedInteger>, Zeroizing<UnsignedInteger>),
  k_i: (Zeroizing<<P as Parameters<PCG>>::F>, Zeroizing<<P as Parameters<PCG>>::F>),
  beta_i: Zeroizing<UnsignedInteger>,
  observing: Observing<PCG, CG, P>,
}

/// A view of the first round of the signing protocol.
impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>>
  SigningProtocol<PCG, CG, P>
{
  /// Participate in the 2-round signing protocol.
  ///
  /// Returns the participant's message and the view necessary to further participate.
  #[must_use]
  pub fn participate(
    rng: &mut impl CryptoRng,
    setup: Arc<Setup<PCG, CG, P>>,
  ) -> (Participating<PCG, CG, P>, Vec<u8>)
  where
    P: Parameters<CG, E = <P as Parameters<PCG>>::E>,
  {
    // Create the view of the protocol
    let mut observing = Self::observe(setup.view().clone());

    // Participate in it
    const PROTOCOL_ELEMENTS_SIZE_ESTIMATE: usize = 3 * 384;
    const CLASS_GROUPS_PROOF_SIZE_ESTIMATE: usize = (6 * 384) + 32 + (2 * 64);
    let mut message =
      Vec::with_capacity(PROTOCOL_ELEMENTS_SIZE_ESTIMATE + CLASS_GROUPS_PROOF_SIZE_ESTIMATE);
    let (alpha_i, k_i, beta_i) = {
      let mut message = DigestWriter(observing.transcript.clone(), &mut message);

      let (alpha_i, k_i) = {
        // Sample the nonce
        let k_i = (
          Zeroizing::new(<P as Parameters<PCG>>::F::random(&mut *rng)),
          Zeroizing::new(<P as Parameters<PCG>>::F::random(&mut *rng)),
        );

        // Write the nonce commitments
        message
          .write_all((<P as Parameters<PCG>>::E::generator() * k_i.0.deref()).to_bytes().as_ref())
          .unwrap();
        message
          .write_all((<P as Parameters<PCG>>::E::generator() * k_i.1.deref()).to_bytes().as_ref())
          .unwrap();

        // Create the ciphertext for it
        let alpha_i = (
          Zeroizing::new(UnsignedInteger::random(
            setup.view().class_group().unknown_order_bound() + 128,
            &mut *rng,
          )),
          Zeroizing::new(UnsignedInteger::random(
            setup.view().class_group().unknown_order_bound() + 128,
            &mut *rng,
          )),
        );
        let alpha_i_bytes =
          (Zeroizing::new(alpha_i.0.to_be_bytes()), Zeroizing::new(alpha_i.1.to_be_bytes()));
        let K_i = (
          PCG::multiexp(
            &setup.view().prover_class_group().identity_p(),
            &[
              (setup.view().prover_G(), &alpha_i_bytes.0),
              (
                setup.view().prover_class_group().f(),
                &Zeroizing::new(crate::be_bytes(k_i.0.deref())),
              ),
            ],
          ),
          PCG::multiexp(
            &setup.view().prover_class_group().identity_p(),
            &[
              (setup.view().prover_G(), &alpha_i_bytes.1),
              (
                setup.view().prover_class_group().f(),
                &Zeroizing::new(crate::be_bytes(k_i.1.deref())),
              ),
            ],
          ),
        );

        // Write the ciphertexts to our message
        K_i.0.compress(&mut message).unwrap();
        K_i.1.compress(&mut message).unwrap();

        (alpha_i, k_i)
      };

      let beta_i = {
        let beta_i = Zeroizing::new(UnsignedInteger::random(
          setup.view().class_group().unknown_order_bound() + 128,
          &mut *rng,
        ));
        let beta_i_bytes = Zeroizing::new(beta_i.to_be_bytes());
        let U_i = PCG::mul(setup.view().prover_G(), &beta_i_bytes);

        // Write the commitment to our message
        U_i.compress(&mut message).unwrap();

        beta_i
      };

      <P as Parameters<PCG>>::RoundOneProofs::prove(
        &mut *rng,
        setup.view().prover_class_group(),
        setup.view().prover_G(),
        (&alpha_i.0, &alpha_i.1),
        (&k_i.0, &k_i.1),
        &beta_i,
        &mut message,
      )
      .unwrap();

      (alpha_i, k_i, beta_i)
    };

    // Because this is the view if we're participating, accumulate our own participation
    match observing.accumulate(rng, setup.i(), message.clone()) {
      Ready::Ready(_) => unreachable!("t == 1 barred at setup"),
      Ready::NotReady((observing_, error)) => {
        observing = observing_;
        assert!(error.is_none());
      }
    }

    (Participating { setup, alpha_i, k_i, beta_i, observing }, message)
  }
  /// Observe the execution of the 2-round signing protocol.
  #[must_use]
  pub fn observe(setup: Arc<SetupView<PCG, CG, P>>) -> Observing<PCG, CG, P> {
    let transcript = setup.transcript();

    Observing {
      setup,
      transcript,
      accumulated: HashMap::new(),
      faulty: HashSet::new(),
      pending: HashMap::new(),
    }
  }
}

/// An error from the first round of the signing protocol.
pub enum RoundOneError {
  /// The participant index was invalid.
  InvalidParticipant,
  /// This participant has already participated.
  AlreadyParticipated,
  /// The following participants were faulty.
  Faults(Vec<Participant>),
}

/// An enum representing an object not ready or now ready.
#[must_use]
pub enum Ready<NotReady, Ready> {
  /// Not ready.
  NotReady(NotReady),
  /// Ready.
  Ready(Ready),
}

/// The view of someone who has observed the first round and can observe signature shares once the
/// message is specified.
// "signature shares" is loosely defined here as the round two messages.
pub struct ObservingSigning<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<SetupView<PCG, CG, P>>,
  transcript: blake3::Hasher,
  rho: Vec<<P as Parameters<PCG>>::F>,
  R: <P as Parameters<PCG>>::E,
  K: CG,
  neg_U: CG,
  lagrange_coefficients: HashMap<Participant, <P as Parameters<PCG>>::F>,
  signing_set: Vec<Participant>,
  K_U_i: HashMap<Participant, ((CG, CG), CG)>,
}

/// The view of someone who has observed the first round and can now produce a signature share.
pub struct Signing<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<Setup<PCG, CG, P>>,
  alpha_i: (Zeroizing<UnsignedInteger>, Zeroizing<UnsignedInteger>),
  rho_i: <P as Parameters<PCG>>::F,
  k_i: Zeroizing<<P as Parameters<PCG>>::F>,
  beta_i: Zeroizing<UnsignedInteger>,
  observing_signing: ObservingSigning<PCG, CG, P>,
}

impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> Observing<PCG, CG, P> {
  /// Accumulate a message from a participant.
  ///
  /// Please see `Participating::accumulate` for more information. This method matches its
  /// behavior.
  pub fn accumulate(
    mut self,
    rng: &mut impl CryptoRng,
    participant: Participant,
    message: Vec<u8>,
  ) -> Ready<(Self, Option<RoundOneError>), ObservingSigning<PCG, CG, P>>
  where
    P: Parameters<CG, E = <P as Parameters<PCG>>::E>,
  {
    // Verify the participant index
    if usize::from(u16::from(participant)) > self.setup.n() {
      return Ready::NotReady((self, Some(RoundOneError::InvalidParticipant)));
    }
    // Verify they haven't already participated
    if self.accumulated.contains_key(&participant) ||
      self.faulty.contains(&participant) ||
      self.pending.contains_key(&participant)
    {
      return Ready::NotReady((self, Some(RoundOneError::AlreadyParticipated)));
    }
    // Mark their message as pending
    self.pending.insert(participant, message);

    // If we're now at the threshold, batch verify the pending messages and move them to
    // accumulated
    let mut faulty = HashSet::new();
    if (self.accumulated.len() + self.pending.len()) == usize::from(self.setup.t()) {
      let mut messages = HashMap::with_capacity(self.pending.len());

      // Prepare the batch verifications
      let mut round_one_batch_verifier =
        <P as Parameters<CG>>::RoundOneProofs::batch_verifier(self.pending.len());
      for (participant, message) in self.pending.drain() {
        let message = message.as_slice();
        let mut message = DigestReader(self.transcript.clone(), message);

        let Ok(R_i_0) = <P as Parameters<PCG>>::read_canonical_E(&mut message) else {
          faulty.insert(participant);
          continue;
        };
        let Ok(R_i_1) = <P as Parameters<PCG>>::read_canonical_E(&mut message) else {
          faulty.insert(participant);
          continue;
        };
        let R_i = (R_i_0, R_i_1);

        let Ok(K_i_0) = CG::decompress(&mut message, self.setup.class_group().delta_p()) else {
          faulty.insert(participant);
          continue;
        };
        let Ok(K_i_1) = CG::decompress(&mut message, self.setup.class_group().delta_p()) else {
          faulty.insert(participant);
          continue;
        };
        let K_i = (K_i_0, K_i_1);

        let Ok(U_i) = CG::decompress(&mut message, self.setup.class_group().delta_p()) else {
          faulty.insert(participant);
          continue;
        };

        let Ok(()) = <P as Parameters<CG>>::RoundOneProofs::queue_verification(
          &mut *rng,
          &mut round_one_batch_verifier,
          participant,
          self.setup.class_group(),
          R_i,
          K_i.clone(),
          U_i.clone(),
          &mut message,
        ) else {
          faulty.insert(participant);
          continue;
        };

        messages.insert(participant, (message.0, R_i, K_i, U_i));
      }

      // Perform the batch verification
      match <P as Parameters<CG>>::RoundOneProofs::verify(
        self.setup.class_group(),
        self.setup.G(),
        round_one_batch_verifier,
      ) {
        Ok(()) => {}
        Err(faults) => {
          for fault in faults {
            faulty.insert(fault);
          }
        }
      }

      // Move forward with the valid messages
      for (participant, values) in messages {
        if faulty.contains(&participant) {
          continue;
        }

        self.accumulated.insert(participant, values);
      }
    }

    // Fold the faulty participants from this verification run into our state
    for faulty in &faulty {
      self.faulty.insert(*faulty);
    }

    // If we've accumulated `t` messages, move to round two
    if self.accumulated.len() == usize::from(self.setup.t()) {
      // Since we run upon `t` potentially valid messages, `t` valid should mean none were invalid
      debug_assert!(faulty.is_empty());

      let mut signing_set = self.accumulated.keys().copied().collect::<Vec<_>>();
      signing_set.sort();

      // Calculate the binding factor
      let mut R_K_U_i = HashMap::new();
      for participant in &signing_set {
        let (transcript, R_i, K_i, U_i) = self.accumulated.remove(participant).unwrap();
        // Fold this transcript back into our own transcript
        self.transcript.update(&u16::from(*participant).to_le_bytes());
        self.transcript.update(&<[u8; 32]>::from(transcript.finalize()));
        R_K_U_i.insert(*participant, (R_i, K_i, U_i));
      }

      // Calculate the sums of the contributions
      let mut rho: Vec<<P as Parameters<PCG>>::F> = Vec::with_capacity(signing_set.len());
      let mut R = None;
      let mut K_0: Option<CG> = None;
      let mut K_1 = Vec::with_capacity(signing_set.len());
      let mut U: Option<CG> = None;
      let mut K_U_i = HashMap::new();
      for participant in &signing_set {
        let rho_i = <P as Parameters<PCG>>::from_xof(self.transcript.finalize_xof());
        self.transcript.update(&[0]);
        rho.push(rho_i);

        let (R_i, K_i, U_i) = R_K_U_i.remove(participant).unwrap();
        let R_i = R_i.0 + (R_i.1 * rho_i);

        R = R.map(|existing| existing + R_i).or(Some(R_i));
        K_0 = K_0.map(|K_0| K_0.add(&K_i.0)).or_else(|| Some(K_i.0.clone()));
        K_1.push((
          Table::new_for_scalar_bits(
            256,
            self.setup.class_group().identity_p().clone(),
            K_i.1.clone(),
          ),
          crate::be_bytes(&rho_i),
        ));
        U = U.map(|U| U.add(&U_i)).or_else(|| Some(U_i.clone()));

        K_U_i.insert(*participant, (K_i, U_i));
      }
      let K = K_0.unwrap().add(&CG::multiexp(
        &self.setup.class_group().identity_p(),
        &K_1.iter().map(|(K_1, rho)| (K_1, rho.as_slice())).collect::<Vec<_>>(),
      ));

      return Ready::Ready(ObservingSigning {
        setup: self.setup,
        transcript: self.transcript,
        rho,
        R: R.unwrap(),
        K,
        neg_U: -U.unwrap(),
        lagrange_coefficients: signing_set
          .iter()
          .copied()
          .map(|i| {
            let i_f = <P as Parameters<PCG>>::F::from(u64::from(u16::from(i)));

            let mut num = <P as Parameters<PCG>>::F::ONE;
            let mut denom = <P as Parameters<PCG>>::F::ONE;
            for l in &signing_set {
              if i == *l {
                continue;
              }

              let share = <P as Parameters<PCG>>::F::from(u64::from(u16::from(*l)));
              num *= share;
              denom *= share - i_f;
            }

            // Safe as this will only be 0 if we're part of the above loop
            // (which we have an if case to avoid)
            let lagrange = num * denom.invert().unwrap();
            (i, lagrange)
          })
          .collect(),
        signing_set,
        K_U_i,
      });
    }

    Ready::NotReady((
      self,
      if faulty.is_empty() {
        None
      } else {
        Some(RoundOneError::Faults(faulty.into_iter().collect()))
      },
    ))
  }
}

impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>>
  Participating<PCG, CG, P>
{
  /// Accumulate a message from a participant.
  ///
  /// This message is expected to be authenticated as originating from the sender by the caller.
  ///
  /// The signing set is considered the first `t` signers who provide valid messages. If the
  /// signing set was determined before any participation, the caller is expected to only
  /// accumulate messages from participants within the signing set.
  ///
  /// This will return itself and still be usable to perform accumulation even if the message is
  /// invalid. This flow enables determining the signing set to be the first `t` signers who
  /// publish valid messages. Such determination would be delayed specification of the signing set
  /// and is accordingly subject to the long commentary present on `SigningProtocol::participate`.
  pub fn accumulate(
    mut self,
    rng: &mut impl CryptoRng,
    participant: Participant,
    message: Vec<u8>,
  ) -> Ready<(Self, Option<RoundOneError>), Signing<PCG, CG, P>>
  where
    P: Parameters<CG, E = <P as Parameters<PCG>>::E>,
  {
    match self.observing.accumulate(rng, participant, message) {
      Ready::Ready(observing_signing) => {
        let rho_i = observing_signing.rho
          [observing_signing.signing_set.iter().position(|i| *i == self.setup.i()).unwrap()];
        Ready::Ready(Signing {
          setup: self.setup,
          alpha_i: self.alpha_i,
          rho_i,
          k_i: Zeroizing::new((rho_i * self.k_i.1.deref()) + self.k_i.0.deref()),
          beta_i: self.beta_i,
          observing_signing,
        })
      }
      Ready::NotReady((observing, error)) => {
        self.observing = observing;
        Ready::NotReady((self, error))
      }
    }
  }
}

/// The view of someone aggregating signature shares to obtain the resulting signature.
pub struct Aggregating<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> {
  observing_signing: ObservingSigning<PCG, CG, P>,
  x_coordinate: <P as Parameters<PCG>>::F,
  message_hash: <P as Parameters<PCG>>::F,
  Z: CG,

  pending: HashMap<Participant, Vec<u8>>,
}

impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>>
  ObservingSigning<PCG, CG, P>
{
  /// Observe the signing of the following message.
  #[must_use]
  pub fn message(mut self, message: &[u8]) -> Aggregating<PCG, CG, P> {
    // We don't transcript this as it's deterministic to the transcripted nonce commitment
    let x_coordinate = <P as Parameters<PCG>>::x_coordinate(&self.R);

    let message_hash = <P as Parameters<PCG>>::hash_message(message);
    // Transcript the message (hash)
    self.transcript.update(message_hash.to_repr().as_ref());

    let mut C = vec![];
    for (participant, lagrange) in &self.lagrange_coefficients {
      let share_ciphertext = self
        .setup
        .share_ciphertext(*participant)
        .expect("didn't have the share ciphertext for a participant");
      let lagrange_bytes = crate::be_bytes(lagrange);
      C.push((share_ciphertext, lagrange_bytes));
    }
    // We don't transcript this as it's deterministic to the transcripted setup + signing set
    let C = CG::multiexp(
      &self.setup.class_group().identity_p(),
      &C.iter()
        .map(|(share_ciphertext, lagrange_bytes)| (*share_ciphertext, lagrange_bytes.as_slice()))
        .collect::<Vec<_>>(),
    );

    // Panics with negligible probability
    let message_derivative = message_hash * x_coordinate.invert().unwrap();

    // Again, not transcripted as deterministic (and therefore already bound) to the transcript
    let Z = CG::mul(self.setup.class_group().f(), &crate::be_bytes(&message_derivative)).add(&C);

    Aggregating { observing_signing: self, x_coordinate, message_hash, Z, pending: HashMap::new() }
  }
}

impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> Signing<PCG, CG, P> {
  /// Participate in signing the following message.
  ///
  /// Returns the participant's message and the view necessary to obtain the resulting signature.
  ///
  /// Please see `SigningProtocol::participate` for the long commentary on when this must be
  /// determined.
  #[must_use]
  pub fn sign(
    self,
    rng: &mut impl CryptoRng,
    message: &[u8],
  ) -> (Aggregating<PCG, CG, P>, Vec<u8>) {
    let mut aggregating = self.observing_signing.message(message);

    fn scaled_decryption<PCG: ElementExt>(
      A: &Table<PCG>,
      neg_B: &Table<PCG>,
      alpha_i: &UnsignedInteger,
      beta_i: &UnsignedInteger,
    ) -> PCG {
      let identity = &neg_B[0];
      PCG::multiexp(
        identity,
        &[
          (A, &Zeroizing::new(beta_i.to_be_bytes())),
          (neg_B, &Zeroizing::new(alpha_i.to_be_bytes())),
        ],
      )
    }

    const PROTOCOL_ELEMENTS_SIZE_ESTIMATE: usize = 2 * 384;
    const CLASS_GROUPS_PROOF_SIZE_ESTIMATE: usize = (10 * 384) + (4 * 64);
    let message =
      Vec::with_capacity(PROTOCOL_ELEMENTS_SIZE_ESTIMATE + CLASS_GROUPS_PROOF_SIZE_ESTIMATE);
    let mut message = DigestWriter(aggregating.observing_signing.transcript.clone(), message);

    let (delta_i, x_i) = self.setup.share_ciphertext_opening();
    let lagrange = aggregating.observing_signing.lagrange_coefficients[&self.setup.i()];
    let delta_i =
      Zeroizing::new(delta_i * &UnsignedInteger::from_be_slice(&crate::be_bytes(&lagrange)));
    let x_i = Zeroizing::new(lagrange * x_i);

    let K = table_scaled_decryption_ciphertext::<PCG, CG, P>(
      self.setup.view().prover_class_group(),
      aggregating.observing_signing.K.clone(),
    );

    let Z = table_scaled_decryption_ciphertext::<PCG, CG, P>(
      self.setup.view().prover_class_group(),
      aggregating.Z.clone(),
    );

    let neg_U = Table::new_for_scalar_bits(
      2 * usize::try_from(self.setup.view().class_group().unknown_order_bound() + 128).unwrap(),
      self.setup.view().prover_class_group().identity_p().clone(),
      PCG::from(aggregating.observing_signing.neg_U.clone()),
    );

    // (H(m)*r**-1 + x) * u
    scaled_decryption::<PCG>(&Z, &neg_U, &delta_i, &self.beta_i).compress(&mut message).unwrap();
    // k * u
    let alpha_i = Zeroizing::new(
      self.alpha_i.0.deref() +
        &Zeroizing::new(
          &UnsignedInteger::from_be_slice(&crate::be_bytes(&self.rho_i)) * &self.alpha_i.1,
        ),
    );
    scaled_decryption::<PCG>(&K, &neg_U, &alpha_i, &self.beta_i).compress(&mut message).unwrap();

    <P as Parameters<PCG>>::RoundTwoProofs::prove(
      &mut *rng,
      self.setup.view().prover_class_group(),
      self.setup.view().prover_G(),
      &Z,
      &K,
      &neg_U,
      &delta_i,
      &x_i,
      &alpha_i,
      &self.k_i,
      &self.beta_i,
      &mut message,
    )
    .unwrap();

    // Because this is the view if we're participating, accumulate our own signature share
    match aggregating.aggregate(rng, self.setup.i(), message.1.clone()) {
      Ready::Ready(_) => unreachable!("t == 1 barred at setup"),
      Ready::NotReady((aggregating_, error)) => {
        aggregating = aggregating_;
        assert!(error.is_none());
      }
    }

    (aggregating, message.1)
  }
}

/// An error from the second round of the signing protocol due to how it was called.
pub enum RoundTwoCallerError {
  /// This participant has already participated.
  AlreadyParticipated,
  /// The signature share was not from someone participating in this signing protocol.
  NotAParticipant,
}

/// An ECDSA signature.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Signature<F: PrimeFieldBits> {
  r: F,
  s: F,
}

impl<F: PrimeFieldBits> Signature<F> {
  /// The x-coordinate of the nonce commitment, reduced into the scalar field.
  pub fn r(&self) -> F {
    self.r
  }
  /// The response to the challenge.
  pub fn s(&self) -> F {
    self.s
  }
}

impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> Aggregating<PCG, CG, P> {
  /// Aggregate a signature share from a participant.
  ///
  /// This message is expected to be authenticated as originating from the sender by the caller.
  ///
  /// If any faults are returned, this will never produce a signature. `self` isn't consumed even
  /// if faults are returned so that other messages may still be checked for if they're faulty or
  /// not.
  ///
  /// If a signature is returned, no messages were faulty.
  pub fn aggregate(
    mut self,
    rng: &mut impl CryptoRng,
    participant: Participant,
    message: Vec<u8>,
  ) -> Ready<
    (Self, Option<RoundTwoCallerError>),
    Result<Signature<<P as Parameters<PCG>>::F>, Vec<Participant>>,
  > {
    // Verify they haven't already participated
    if self.pending.contains_key(&participant) {
      return Ready::NotReady((self, Some(RoundTwoCallerError::AlreadyParticipated)));
    }
    // Verify they were in the signing set
    if !self.observing_signing.lagrange_coefficients.contains_key(&participant) {
      return Ready::NotReady((self, Some(RoundTwoCallerError::NotAParticipant)));
    }
    // Mark their message as pending
    self.pending.insert(participant, message);

    // If we're now at the threshold, attempt to yield the signature
    let setup = &self.observing_signing.setup;
    if self.pending.len() == usize::from(setup.t()) {
      let mut faulty = vec![];
      let mut ZU: Option<CG> = None;
      let mut KU: Option<CG> = None;
      let mut messages = HashMap::new();
      for (participant, message) in self.pending.drain() {
        // We use a Cursor so this isn't `&mut &[u8]` yet a fully owned object
        let message = std::io::Cursor::new(message);
        let mut message = DigestReader(self.observing_signing.transcript.clone(), message);

        let Ok(ZU_i) = CG::decompress(&mut message, setup.class_group().delta_p()) else {
          faulty.push(participant);
          continue;
        };
        let Ok(KU_i) = CG::decompress(&mut message, setup.class_group().delta_p()) else {
          faulty.push(participant);
          continue;
        };

        ZU = ZU.map(|ZU| ZU.add(&ZU_i)).or(Some(ZU_i.clone()));
        KU = KU.map(|KU| KU.add(&KU_i)).or(Some(KU_i.clone()));
        messages.insert(participant, (message, ZU_i, KU_i));
      }

      if faulty.is_empty() {
        let be_bytes_to_scalar = |bytes| {
          let mut res = <P as Parameters<PCG>>::F::ZERO;
          for b in bytes {
            for _ in 0 .. 8 {
              res = res.double();
            }
            res += <P as Parameters<PCG>>::F::from(u64::from(b));
          }
          res
        };

        let discrete_logarithm = |element: CG| {
          let log = setup.class_group().discrete_logarithm(&element).unwrap();
          be_bytes_to_scalar(log)
        };

        // This is `(H(m)*r**-1 + x) * u`, so we need to scale it by `r` for `(H(m) + rx) * u`
        let numerator = discrete_logarithm(ZU.unwrap());
        let numerator = numerator * self.x_coordinate;
        let denominator = discrete_logarithm(KU.unwrap());

        let r = self.x_coordinate;
        let s = numerator * denominator.invert().unwrap();

        // If we produced a valid signature, don't verify the proofs and simply yield the signature
        // A valid signature means the protocol elements were correct, ignoring possible malleation
        // s = (H(m) + rx)/k
        // sR = (H(m) + rx)/k * kG = (H(m) + rx)G
        let lhs = self.observing_signing.R * s;
        let rhs = (<P as Parameters<PCG>>::E::generator() * self.message_hash) +
          (setup.verification_key() * self.x_coordinate);
        if lhs == rhs {
          return Ready::Ready(Ok(Signature { r, s }));
        }
      }

      // Verify the proofs to identify any other faulty participants
      let bits = usize::try_from(setup.class_group().unknown_order_bound()).unwrap();
      let neg_U = Table::new_for_scalar_bits(
        bits,
        setup.class_group().identity_p().clone(),
        self.observing_signing.neg_U.clone(),
      );
      let Z =
        Table::new_for_scalar_bits(bits, setup.class_group().identity_p().clone(), self.Z.clone());
      let K = Table::new_for_scalar_bits(
        bits,
        setup.class_group().identity_p().clone(),
        self.observing_signing.K.clone(),
      );
      for (participant, (mut transcript, ZU_i, KU_i)) in messages {
        let (K_i, U_i) = self.observing_signing.K_U_i.remove(&participant).unwrap();
        // We do calculate Z prior, but not Z_i prior, so we calculcate this here
        let Z_i = CG::mul(
          setup.share_ciphertext(participant).unwrap(),
          &crate::be_bytes(&self.observing_signing.lagrange_coefficients[&participant]),
        );
        if <P as Parameters<CG>>::RoundTwoProofs::verify(
          rng,
          setup.class_group(),
          setup.G(),
          &Z,
          &K,
          &neg_U,
          Z_i,
          K_i.0.add(&CG::mul(
            &Table::new_for_scalar_bits(
              <P as Parameters<PCG>>::F::NUM_BITS.try_into().unwrap(),
              setup.class_group().identity_p().clone(),
              K_i.1,
            ),
            &crate::be_bytes(
              &self.observing_signing.rho[self
                .observing_signing
                .signing_set
                .iter()
                .position(|i| *i == participant)
                .expect("non-participating participant in messages")],
            ),
          )),
          U_i,
          ZU_i,
          KU_i,
          &mut transcript,
        )
        .is_err()
        {
          faulty.push(participant);
        }
      }
      return Ready::Ready(Err(faulty));
    }

    Ready::NotReady((self, None))
  }
}
