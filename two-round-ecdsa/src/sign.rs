use core::{marker::PhantomData, ops::Deref};
use std::{
  sync::Arc,
  collections::{HashSet, HashMap},
};

use zeroize::Zeroizing;
use rand::CryptoRng;

use group::{
  ff::{Field, PrimeField, PrimeFieldBits},
  Group,
};
use class_groups::{Element, Table, ClassGroup};

use dkg::Participant;

use crate::{
  UnsignedInteger, DigestReader, DigestWriter, Evrf, RoundOneProofs, RoundTwoProofs, Parameters,
  SetupView, Setup,
};

/// Table a ciphertext for scaled decryption.
///
/// This just yields the presumably-optimal table sizes.
fn table_scaled_decryption_ciphertext<
  PCG: Element,
  CG: Element,
  P: Parameters<PCG> + Parameters<CG>,
>(
  class_group: &ClassGroup<PCG>,
  ciphertext: &(CG, CG),
) -> (Table<PCG>, Table<PCG>) {
  let ciphertext = (class_group.map_p(&ciphertext.0), class_group.map_p(&ciphertext.1));

  (
    Table::new_for_scalar_bits(
      // We `2 *` the bits as we do one scaling for the protocol itself and the proofs presumably
      // also do one
      2 * usize::try_from(class_group.unknown_order_bound() + 128).unwrap(),
      class_group.identity_p().clone(),
      ciphertext.0,
    ),
    Table::new_for_scalar_bits(
      // The protocol scales by an elliptic curve scalar yet the proofs presumably scale by a
      // uniform-to-the-class-group scalar
      usize::try_from(<P as Parameters<PCG>>::F::NUM_BITS).unwrap() +
        usize::try_from(class_group.unknown_order_bound() + 128).unwrap(),
      class_group.identity_p().clone(),
      ciphertext.1,
    ),
  )
}

/// The 2-round signing protocol.
pub struct SigningProtocol<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>>(
  PhantomData<(PCG, CG, P)>,
);

/// A view of someone observing the signing protocol.
pub struct Observing<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<SetupView<PCG, CG, P>>,
  transcript: blake3::Hasher,
  evrf_context: <<P as Parameters<PCG>>::Evrf as Evrf<PCG, P>>::Context,
  accumulated: HashMap<Participant, (blake3::Hasher, <P as Parameters<PCG>>::E, (CG, CG), CG)>,
  faulty: HashSet<Participant>,
  pending: HashMap<Participant, Vec<u8>>,
}

/// A view of someone participating in the signing protocol.
pub struct Participating<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<Setup<PCG, CG, P>>,
  alpha_i: Zeroizing<UnsignedInteger>,
  beta_i: Zeroizing<UnsignedInteger>,
  u_i: Zeroizing<<P as Parameters<PCG>>::F>,
  observing: Observing<PCG, CG, P>,
}

/// A view of the first round of the signing protocol.
impl<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> SigningProtocol<PCG, CG, P> {
  /// The recommended `session_id` structure.
  ///
  /// Alternative `session_id`s may or may not be secure but no others are recommended/endorsed.
  /// Please see `SigningProtocol::participate`'s documentation.
  ///
  /// The caller is expected to enforce that only this signing set has its messages passed to
  /// `ObservingSigning::accumulate`/`Signing::accumulate`.
  pub fn recommended_session_id(participants: &HashSet<Participant>, message: &[u8]) -> [u8; 32] {
    let mut participants = participants.iter().copied().collect::<Vec<_>>();
    participants.sort();

    let mut hasher = blake3::Hasher::new();
    hasher.update(
      &u16::try_from(participants.len())
        .expect("Participant only has 2**16-1 values yet set size exceeded 2**16-1")
        .to_le_bytes(),
    );
    for participant in participants {
      hasher.update(&u16::from(participant).to_le_bytes());
    }
    // This is variable length yet we immediately draw a digest after, so there's nothing to
    // malleate it with
    hasher.update(message);
    hasher.finalize().into()
  }

  /// Participate in the 2-round signing protocol.
  ///
  /// Returns the participant's message and the view necessary to further participate.
  ///
  /// `session_id` must be carefully chosen. The simplest choice is the signing set and the
  /// message. This is a secure choice of `session_id` and the recommended choice, offered by
  /// `SigningProtocol::recommended_session_id`. Reuse of `session_id` across signing sets/messages
  /// will leak the private key.
  ///
  /// If delayed specification of signing set is desired, then `session_id` should be some
  /// derivative of `(message, attempt number)` where only a single signing set will be specified
  /// and moved forward with per attempt.
  ///
  /// If delayed specification of the message is desired (and optionally also the signing set),
  /// then this should be some derivative of a global index where each index will only be used for
  /// a single message (and signing set).
  ///
  /// Delayed specification of the signing set/message was not proven secure in the paper.
  /// Post-specification of the signing set allows an adversary to bias the nonce via choice of
  /// set (as different sets will produce distinct nonces). Post-specification of the message is
  /// known to enable attacks on certain multisignature scheme
  /// (<https://eprint.iacr.org/2024/437>), even with simulatable nonces.
  ///
  /// There is supporting evidence that the ROS problem is hard for ECDSA in
  /// <https://eprint.iacr.org/2021/1449>. That would imply post-specification of
  /// signing set/message may be without issue, so long as a session ID is never reused.
  ///
  /// This code defers the derivation of session ID, and specification timeline, to the caller in
  /// order to enable these features if proven secure. The caller is trusted with the important,
  /// critical, and difficult responsibility of handling this securely. The only endorsed solution
  /// is a session ID generated via `SigningProtocol::recommended_session_id` where only the
  /// specified signing set has their messages accumulated.
  #[must_use]
  pub fn participate(
    rng: &mut impl CryptoRng,
    setup: Arc<Setup<PCG, CG, P>>,
    session_id: [u8; 32],
  ) -> (Participating<PCG, CG, P>, Vec<u8>)
  where
    P: Parameters<CG, E = <P as Parameters<PCG>>::E>,
  {
    // Create the view of the protocol
    let mut observing = Self::observe(setup.view().clone(), session_id);

    // Participate in it
    const EVRF_SIZE_ESTIMATE: usize = 32 + 768;
    const PROTOCOL_ELEMENTS_SIZE_ESTIMATE: usize = 3 * 384;
    const CLASS_GROUPS_PROOF_SIZE_ESTIMATE: usize = (6 * 384) + 32 + (2 * 64);
    let mut message = Vec::with_capacity(
      EVRF_SIZE_ESTIMATE + PROTOCOL_ELEMENTS_SIZE_ESTIMATE + CLASS_GROUPS_PROOF_SIZE_ESTIMATE,
    );
    let (alpha_i, beta_i, u_i) = {
      let mut message = DigestWriter(observing.transcript.clone(), &mut message);

      let (alpha_i, nonce_i) = {
        // Sample the nonce
        let nonce_i = <P as Parameters<PCG>>::Evrf::prove(
          &mut *rng,
          setup.view().evrf_global_setup(),
          setup.evrf_setup(),
          &observing.evrf_context,
          &mut message,
        )
        .unwrap();

        // Create the ciphertext for it
        let alpha_i = Zeroizing::new(UnsignedInteger::random(
          setup.view().class_group().unknown_order_bound() + 128,
          &mut *rng,
        ));
        let alpha_i_bytes = Zeroizing::new(alpha_i.to_be_bytes());
        let K_tilde_i = (
          CG::mul(setup.view().G(), &alpha_i_bytes),
          CG::multiexp(
            setup.view().class_group().identity_p(),
            &[
              (setup.view().Y(), &alpha_i_bytes),
              (setup.view().class_group().f(), &Zeroizing::new(crate::be_bytes(nonce_i.deref()))),
            ],
          ),
        );

        // Write the ciphertext to our message
        K_tilde_i.0.compress(&mut message).unwrap();
        K_tilde_i.1.compress(&mut message).unwrap();

        (alpha_i, nonce_i)
      };

      let (beta_i, u_i) = {
        // Sample the multiplicative blinding factor
        let u_i = Zeroizing::new(<P as Parameters<PCG>>::F::random(&mut *rng));

        // Create the commitment for it
        let beta_i = Zeroizing::new(UnsignedInteger::random(
          setup.view().class_group().unknown_order_bound() + 128,
          &mut *rng,
        ));
        let beta_i_bytes = Zeroizing::new(beta_i.to_be_bytes());
        let U_i = CG::multiexp(
          setup.view().class_group().identity_p(),
          &[
            (setup.view().G(), &beta_i_bytes),
            (setup.view().Y(), &Zeroizing::new(crate::be_bytes(u_i.deref()))),
          ],
        );

        // Write the commitment to our message
        U_i.compress(&mut message).unwrap();

        (beta_i, u_i)
      };

      <P as Parameters<PCG>>::RoundOneProofs::prove(
        &mut *rng,
        setup.view().prover_class_group(),
        setup.view().prover_G(),
        setup.view().prover_Y(),
        &alpha_i,
        &nonce_i,
        &beta_i,
        &u_i,
        &mut message,
      )
      .unwrap();

      (alpha_i, beta_i, u_i)
    };

    // Because this is the view if we're participating, accumulate our own participation
    match observing.accumulate(rng, setup.i(), message.clone()) {
      Ready::Ready(_) => unreachable!("t == 1 barred at setup"),
      Ready::NotReady((observing_, error)) => {
        observing = observing_;
        assert!(error.is_none());
      }
    }

    (Participating { setup, alpha_i, beta_i, u_i, observing }, message)
  }
  /// Observe the execution of the 2-round signing protocol.
  #[must_use]
  pub fn observe(setup: Arc<SetupView<PCG, CG, P>>, session_id: [u8; 32]) -> Observing<PCG, CG, P> {
    let mut transcript = setup.transcript();
    transcript.update(&session_id);

    let evrf_context =
      <P as Parameters<PCG>>::Evrf::context(setup.evrf_global_setup(), &mut transcript);
    Observing {
      setup,
      transcript,
      evrf_context,
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
pub struct ObservingSigning<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<SetupView<PCG, CG, P>>,
  transcript: blake3::Hasher,
  R: <P as Parameters<PCG>>::E,
  K_tilde: (CG, CG),
  neg_U: CG,
  lagrange_coefficients: HashMap<Participant, <P as Parameters<PCG>>::F>,
  K_tilde_i_0_U_i: HashMap<Participant, (CG, CG)>,
}

/// The view of someone who has observed the first round and can now produce a signature share.
pub struct Signing<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> {
  setup: Arc<Setup<PCG, CG, P>>,
  alpha_i: Zeroizing<UnsignedInteger>,
  beta_i: Zeroizing<UnsignedInteger>,
  u_i: Zeroizing<<P as Parameters<PCG>>::F>,
  observing_signing: ObservingSigning<PCG, CG, P>,
}

impl<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> Observing<PCG, CG, P> {
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
      let mut evrf_batch_verifier =
        <P as Parameters<PCG>>::Evrf::batch_verifier(self.setup.evrf_global_setup());
      let mut round_one_batch_verifier =
        <P as Parameters<CG>>::RoundOneProofs::batch_verifier(self.pending.len());
      for (participant, message) in self.pending.drain() {
        let message = message.as_slice();
        let mut message = DigestReader(self.transcript.clone(), message);

        let Ok(R_i) = <P as Parameters<PCG>>::Evrf::queue_verification(
          &mut *rng,
          self.setup.evrf_global_setup(),
          &mut evrf_batch_verifier,
          participant,
          self.setup.evrf_setup(&participant).unwrap(),
          &self.evrf_context,
          &mut message,
        ) else {
          faulty.insert(participant);
          continue;
        };

        let Ok(K_tilde_i_0) = self.setup.class_group().decompress_p(&mut message) else {
          faulty.insert(participant);
          continue;
        };
        let Ok(K_tilde_i_1) = self.setup.class_group().decompress_p(&mut message) else {
          faulty.insert(participant);
          continue;
        };
        let K_tilde_i = (K_tilde_i_0, K_tilde_i_1);
        let Ok(U_i) = self.setup.class_group().decompress_p(&mut message) else {
          faulty.insert(participant);
          continue;
        };

        let Ok(()) = <P as Parameters<CG>>::RoundOneProofs::queue_verification(
          &mut *rng,
          &mut round_one_batch_verifier,
          participant,
          self.setup.class_group(),
          R_i,
          K_tilde_i.clone(),
          U_i.clone(),
          &mut message,
        ) else {
          faulty.insert(participant);
          continue;
        };

        messages.insert(participant, (message.0, R_i, K_tilde_i, U_i));
      }

      // Perform the batch verifications
      match <P as Parameters<PCG>>::Evrf::verify(
        self.setup.evrf_global_setup(),
        evrf_batch_verifier,
      ) {
        Ok(()) => {}
        Err(faults) => {
          for fault in faults {
            faulty.insert(fault);
          }
        }
      }
      match <P as Parameters<CG>>::RoundOneProofs::verify(
        self.setup.class_group(),
        self.setup.G(),
        self.setup.Y(),
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

      // Calculate the sums of the contributions
      let mut R = None;
      let mut K_tilde: Option<(CG, CG)> = None;
      let mut U: Option<CG> = None;
      let mut K_tilde_i_0_U_i = HashMap::new();
      for participant in &signing_set {
        let (transcript, R_i, K_tilde_i, U_i) = self.accumulated.remove(participant).unwrap();
        // Fold this transcript back into our own transcript
        self.transcript.update(&u16::from(*participant).to_le_bytes());
        self.transcript.update(&<[u8; 32]>::from(transcript.finalize()));

        // The usage of None avoids an `identity + E` group op, even if it is a bit ugly
        R = R.map(|existing| existing + R_i).or(Some(R_i));
        K_tilde = K_tilde
          .map(|K_tilde| (K_tilde.0.add(&K_tilde_i.0), K_tilde.1.add(&K_tilde_i.1)))
          .or(Some((K_tilde_i.0.clone(), K_tilde_i.1)));
        U = U.map(|U| U.add(&U_i)).or(Some(U_i.clone()));

        K_tilde_i_0_U_i.insert(*participant, (K_tilde_i.0, U_i));
      }

      return Ready::Ready(ObservingSigning {
        setup: self.setup,
        transcript: self.transcript,
        R: R.unwrap(),
        K_tilde: K_tilde.unwrap(),
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
        K_tilde_i_0_U_i,
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

impl<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> Participating<PCG, CG, P> {
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
      Ready::Ready(observing_signing) => Ready::Ready(Signing {
        setup: self.setup,
        alpha_i: self.alpha_i,
        beta_i: self.beta_i,
        u_i: self.u_i,
        observing_signing,
      }),
      Ready::NotReady((observing, error)) => {
        self.observing = observing;
        Ready::NotReady((self, error))
      }
    }
  }
}

/// The view of someone aggregating signature shares to obtain the resulting signature.
pub struct Aggregating<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> {
  observing_signing: ObservingSigning<PCG, CG, P>,
  x_coordinate: <P as Parameters<PCG>>::F,
  message_hash: <P as Parameters<PCG>>::F,
  Z_tilde: (CG, CG),

  pending: HashMap<Participant, Vec<u8>>,
}

impl<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> ObservingSigning<PCG, CG, P> {
  /// Observe the signing of the following message.
  #[must_use]
  pub fn message(mut self, message: &[u8]) -> Aggregating<PCG, CG, P> {
    // We don't transcript this as it's deterministic to the transcripted nonce commitment
    let x_coordinate = <P as Parameters<PCG>>::x_coordinate(&self.R);

    let message_hash = <P as Parameters<PCG>>::hash_message(message);
    // Transcript the message (hash)
    /*
      This may already be hashed as part of the `session_id` yet this code doesn't make that
      assumption, and here is where the code first gets access to the message as it's where the
      message is first needed by the protocol (even if prior needed by the security proofs)
    */
    self.transcript.update(message_hash.to_repr().as_ref());

    let mut C_tilde: Option<(CG, CG)> = None;
    for (participant, lagrange) in &self.lagrange_coefficients {
      let share_ciphertext = self
        .setup
        .share_ciphertext(participant)
        .expect("didn't have the share ciphertext for a participant");
      let lagrange_bytes = crate::be_bytes(lagrange);
      let share_ciphertext = (
        CG::mul(&share_ciphertext.0, &lagrange_bytes),
        CG::mul(&share_ciphertext.1, &lagrange_bytes),
      );
      C_tilde = C_tilde
        .map(|existing| (existing.0.add(&share_ciphertext.0), existing.1.add(&share_ciphertext.1)))
        .or_else(|| Some(share_ciphertext.clone()));
    }
    // We don't transcript this as it's deterministic to the transcripted setup + signing set
    let C_tilde = C_tilde.unwrap();

    // Panics with negligible probability
    let message_derivative = message_hash * x_coordinate.invert().unwrap();

    // Again, not transcripted as deterministic (and therefore already bound) to the transcript
    let Z_tilde = (
      C_tilde.0,
      CG::mul(self.setup.class_group().f(), &crate::be_bytes(&message_derivative)).add(&C_tilde.1),
    );

    Aggregating {
      observing_signing: self,
      x_coordinate,
      message_hash,
      Z_tilde,
      pending: HashMap::new(),
    }
  }
}

impl<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> Signing<PCG, CG, P> {
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

    fn scaled_decryption<PCG: Element, P: Parameters<PCG>>(
      A_tilde: &(Table<PCG>, Table<PCG>),
      neg_B: &Table<PCG>,
      alpha_i: &UnsignedInteger,
      beta_i: &UnsignedInteger,
      b_i: &<P as Parameters<PCG>>::F,
    ) -> PCG {
      let identity = &neg_B[0];
      PCG::multiexp(
        identity,
        &[
          (&A_tilde.1, &Zeroizing::new(crate::be_bytes(b_i))),
          (neg_B, &Zeroizing::new(alpha_i.to_be_bytes())),
          (&A_tilde.0, &Zeroizing::new(beta_i.to_be_bytes())),
        ],
      )
    }

    const PROTOCOL_ELEMENTS_SIZE_ESTIMATE: usize = 2 * 384;
    const CLASS_GROUPS_PROOF_SIZE_ESTIMATE: usize = (10 * 384) + (4 * 64);
    let message =
      Vec::with_capacity(PROTOCOL_ELEMENTS_SIZE_ESTIMATE + CLASS_GROUPS_PROOF_SIZE_ESTIMATE);
    let mut message = DigestWriter(aggregating.observing_signing.transcript.clone(), message);

    let delta_i = Zeroizing::new(
      self.setup.share_ciphertext_opening() *
        &UnsignedInteger::from_be_slice(&crate::be_bytes(
          &aggregating.observing_signing.lagrange_coefficients[&self.setup.i()],
        )),
    );

    let K_tilde = table_scaled_decryption_ciphertext::<PCG, CG, P>(
      self.setup.view().prover_class_group(),
      &aggregating.observing_signing.K_tilde,
    );

    let Z_tilde = table_scaled_decryption_ciphertext::<PCG, CG, P>(
      self.setup.view().prover_class_group(),
      &aggregating.Z_tilde,
    );

    let neg_U = Table::new_for_scalar_bits(
      2 * usize::try_from(self.setup.view().class_group().unknown_order_bound() + 128).unwrap(),
      self.setup.view().prover_class_group().identity_p().clone(),
      self.setup.view().prover_class_group().map_p(&aggregating.observing_signing.neg_U),
    );

    // (H(m)*r**-1 + x) * u
    scaled_decryption::<PCG, P>(&Z_tilde, &neg_U, &delta_i, &self.beta_i, &self.u_i)
      .compress(&mut message)
      .unwrap();
    // k * u
    scaled_decryption::<PCG, P>(&K_tilde, &neg_U, &self.alpha_i, &self.beta_i, &self.u_i)
      .compress(&mut message)
      .unwrap();

    <P as Parameters<PCG>>::RoundTwoProofs::prove(
      &mut *rng,
      self.setup.view().prover_class_group(),
      self.setup.view().prover_G(),
      self.setup.view().prover_Y(),
      &Z_tilde,
      &K_tilde,
      &neg_U,
      &delta_i,
      &self.alpha_i,
      &self.beta_i,
      &self.u_i,
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

impl<PCG: Element, CG: Element, P: Parameters<PCG> + Parameters<CG>> Aggregating<PCG, CG, P> {
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

        let Ok(ZU_i) = setup.class_group().decompress_p(&mut message) else {
          faulty.push(participant);
          continue;
        };
        let Ok(KU_i) = setup.class_group().decompress_p(&mut message) else {
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
        self.observing_signing.neg_U,
      );
      let Z_tilde = (
        Table::new_for_scalar_bits(bits, setup.class_group().identity_p().clone(), self.Z_tilde.0),
        Table::new_for_scalar_bits(bits, setup.class_group().identity_p().clone(), self.Z_tilde.1),
      );
      let K_tilde = (
        Table::new_for_scalar_bits(
          bits,
          setup.class_group().identity_p().clone(),
          self.observing_signing.K_tilde.0,
        ),
        Table::new_for_scalar_bits(
          bits,
          setup.class_group().identity_p().clone(),
          self.observing_signing.K_tilde.1,
        ),
      );
      for (participant, (mut transcript, ZU_i, KU_i)) in messages {
        let (K_tilde_i_0, U_i) =
          self.observing_signing.K_tilde_i_0_U_i.remove(&participant).unwrap();
        // We do calculate Z_tilde prior, but not Z_tilde_i prior, so we calculcate this here
        let Z_tilde_i_0 = CG::mul(
          &setup.share_ciphertext(&participant).unwrap().0,
          &crate::be_bytes(&self.observing_signing.lagrange_coefficients[&participant]),
        );
        if <P as Parameters<CG>>::RoundTwoProofs::verify(
          rng,
          setup.class_group(),
          setup.G(),
          setup.Y(),
          &Z_tilde,
          &K_tilde,
          &neg_U,
          Z_tilde_i_0,
          K_tilde_i_0,
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
