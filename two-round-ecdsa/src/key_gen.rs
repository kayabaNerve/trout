use std::{sync::Arc, collections::HashMap};

use zeroize::{Zeroize, Zeroizing};
use rand::{CryptoRng, SeedableRng};
use rand_chacha::ChaCha20Rng;

use group::{
  ff::{Field, PrimeField},
  Group, GroupEncoding,
};
use class_groups::{ElementExt, Table, ClassGroup};

use dkg::Participant;

use crate::{UnsignedInteger, Parameters};

/// The security level to target with the setup.
///
/// These are defined per <https://eprint.iacr.org/2020/196>. Please note a rebuttal of this
/// paper's definition exists in <https://eprint.iacr.org/2021/291>, as its Remark 1.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum SecurityLevel {
  /// An 1827-bit discriminant with 128-bits of security per popular convention.
  ///
  /// This has a 2**-14.3 chance of being weaker than the targeted 128-bit security level.
  OneHundredTwentyEightBit = 0,
  /// A 2048-bit discriminant which should have 128-bits of security even with marginally improved
  /// attacks against class-groups.
  ConservativeOneHundredTwentyEightBit = 1,
  /// A 4096-bit discriminant which only has 128-bits of security in a (2**-64)-case event.
  VeryConservativeOneHundredTwentyEightBit = 2,
  /// A 6784-bit discriminant which only has 128-bits of security in a (2**-128)-case event.
  ExtremelyConservativeOneHundredTwentyEightBit = 3,
  /// A trivial class group which is insecure and MUST only be used for testing purposes.
  Insecure = 0xff,
}

fn class_group<CG: ElementExt, P: Parameters<CG>>(
  seed: [u8; 32],
  security_level: SecurityLevel,
) -> (ClassGroup<CG>, Table<CG>) {
  let mut class_group_rng = ChaCha20Rng::from_seed(seed);

  // The security level is converted to the lambda parameter of which the fundamental
  // discriminant is twice as large
  let lambda = match security_level {
    SecurityLevel::Insecure => 300,
    SecurityLevel::OneHundredTwentyEightBit => 914,
    SecurityLevel::ConservativeOneHundredTwentyEightBit => 1024,
    SecurityLevel::VeryConservativeOneHundredTwentyEightBit => 2048,
    SecurityLevel::ExtremelyConservativeOneHundredTwentyEightBit => 3392,
  };

  let p_bytes = {
    let mut p_bytes = crate::be_bytes(&-P::F::ONE);
    // `p_bytes` has `p - 1` where `p` is prime, so set back the last bit
    const {
      // Handle the edge case of 2 which isn't supported by our class group construction and adding
      // 1 is not the following binary OR operation
      assert!(P::F::NUM_BITS > 1, "prime order was <= 2 when an odd prime is required");
    }
    *p_bytes.last_mut().unwrap() |= 1;
    p_bytes
  };

  let class_group = ClassGroup::<CG>::setup(
    &mut class_group_rng,
    lambda,
    p_bytes.iter().copied().rev().collect::<Vec<_>>(),
  )
  .unwrap();
  let G = class_group.generator_p(&mut class_group_rng);
  // Ensure G is a generator of G_q, not G, as required by the CCYKC proofs
  let G = CG::mul(
    &Table::new_for_scalar_bits(
      P::F::NUM_BITS.try_into().unwrap(),
      class_group.identity_p().clone(),
      G,
    ),
    &p_bytes,
  );
  let G = Table::new(12, class_group.identity_p().clone(), G);

  (class_group, G)
}

/// A view of the setup for a multisig.
#[derive(Clone)]
pub struct SetupView<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> {
  t: u16,
  class_group_seed: [u8; 32],

  prover_class_group: ClassGroup<PCG>,
  prover_G: Table<PCG>,

  class_group: ClassGroup<CG>,
  G: Table<CG>,

  verification_key: <P as Parameters<PCG>>::E,
  // verification_shares: HashMap<Participant, P::E>,
  share_ciphertexts: HashMap<Participant, Table<CG>>,

  // The transcript of this view
  transcript: blake3::Hasher,
}

impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> SetupView<PCG, CG, P> {
  // This is only 'internal' due to assumptions regarding the `HashMap`s
  // They aren't validated with an error returned if they're wrong
  fn new_internal(
    t: u16,
    class_group_seed: [u8; 32],
    security_level: SecurityLevel,
    verification_key: <P as Parameters<PCG>>::E,
    share_ciphertexts: HashMap<Participant, CG>,
  ) -> Self {
    let n = u16::try_from(share_ciphertexts.len()).unwrap();

    // Transcript the parameters for the set
    let mut transcript = blake3::Hasher::new();
    transcript.update(&t.to_le_bytes());
    transcript.update(&n.to_le_bytes());
    transcript.update(&class_group_seed);
    transcript.update(&[security_level as u8]);
    transcript.update(<P as Parameters<PCG>>::E::generator().to_bytes().as_ref());
    transcript.update(verification_key.to_bytes().as_ref());

    // Transcript the per-participant data
    {
      // A buffer we reuse for compressed class-group elements
      let mut buf = Vec::with_capacity(384);
      for participant in (1 ..= n).map(|i| Participant::new(i).unwrap()) {
        let ciphertext = &share_ciphertexts[&participant];

        // These are canonical and self-prefixing, so there's no risk of malleation here
        ciphertext.compress(&mut buf).unwrap();
        transcript.update(&buf);
        buf.clear();
      }
    }

    let (prover_class_group, prover_G) = class_group::<PCG, P>(class_group_seed, security_level);
    let (class_group, G) = class_group::<CG, P>(class_group_seed, security_level);

    let share_ciphertexts = share_ciphertexts
      .into_iter()
      .map(|(participant, C)| (participant, Table::new(12, class_group.identity_p().clone(), C)))
      .collect();

    Self {
      t,
      class_group_seed,

      prover_class_group,
      prover_G,

      class_group,
      G,

      verification_key,
      share_ciphertexts,
      transcript,
    }
  }

  pub(crate) fn t(&self) -> u16 {
    self.t
  }
  pub(crate) fn n(&self) -> usize {
    self.share_ciphertexts.len()
  }
  pub(crate) fn prover_class_group(&self) -> &ClassGroup<PCG> {
    &self.prover_class_group
  }
  pub(crate) fn prover_G(&self) -> &Table<PCG> {
    &self.prover_G
  }
  pub(crate) fn class_group(&self) -> &ClassGroup<CG> {
    &self.class_group
  }
  pub(crate) fn G(&self) -> &Table<CG> {
    &self.G
  }
  /// The ECDSA verification key.
  pub fn verification_key(&self) -> <P as Parameters<PCG>>::E {
    self.verification_key
  }
  pub(crate) fn share_ciphertext(&self, participant: &Participant) -> Option<&Table<CG>> {
    self.share_ciphertexts.get(participant)
  }

  /// The transcript of this view of the setup.
  pub fn transcript(&self) -> blake3::Hasher {
    self.transcript.clone()
  }
}

/// The result of the setup for a participant.
pub struct Setup<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> {
  view: Arc<SetupView<PCG, CG, P>>,
  i: Participant,
  share_ciphertext_opening: Zeroizing<(UnsignedInteger, <P as Parameters<PCG>>::F)>,
}

impl<PCG: ElementExt, CG: ElementExt, P: Parameters<PCG> + Parameters<CG>> Setup<PCG, CG, P> {
  /// The public view of the setup.
  pub fn view(&self) -> &Arc<SetupView<PCG, CG, P>> {
    &self.view
  }

  /// Our participant index.
  pub(crate) fn i(&self) -> Participant {
    self.i
  }

  /// The randomness of our share's ciphertext.
  pub(crate) fn share_ciphertext_opening(&self) -> &(UnsignedInteger, <P as Parameters<PCG>>::F) {
    &self.share_ciphertext_opening
  }

  /// Perform the setup with a dealer key-generation.
  ///
  /// This is not a distributed setup but a trusted setup. The dealer learns the secret key. This
  /// generally should not be used.
  ///
  /// Returns `None` upon invalid parameters.
  #[must_use]
  pub fn dealer(
    rng: &mut impl CryptoRng,
    security_level: SecurityLevel,
    t: u16,
    n: u16,
  ) -> Option<HashMap<Participant, Arc<Setup<PCG, CG, P>>>> {
    {
      let valid_t_n = (t <= n) && (1 < t);
      if !valid_t_n {
        None?;
      }
    }

    let mut class_group_seed = [0; 32];
    rng.fill_bytes(&mut class_group_seed);
    let (class_group, G) = class_group::<CG, P>(class_group_seed, security_level);

    // Generate `t` coefficients
    let mut coeffs = Zeroizing::new(vec![<P as Parameters<PCG>>::F::ZERO; usize::from(t)]);
    for coeff in coeffs.as_mut_slice() {
      *coeff = <P as Parameters<PCG>>::F::random(&mut *rng);
    }

    // Set the verification key
    let verification_key = <P as Parameters<PCG>>::E::generator() * coeffs[0];

    let mut share_ciphertext_openings = HashMap::new();
    for participant in (1 ..= n).map(|i| Participant::new(i).unwrap()) {
      // Create the shares for each participant
      fn polynomial<F: PrimeField + Zeroize>(coefficients: &[F], l: Participant) -> Zeroizing<F> {
        let l = F::from(u64::from(u16::from(l)));
        // This should never be reached since Participant is explicitly non-zero
        assert!(l != F::ZERO, "zero participant passed to polynomial");
        let mut share = Zeroizing::new(F::ZERO);
        for (idx, coefficient) in coefficients.iter().rev().enumerate() {
          *share += coefficient;
          if idx != (coefficients.len() - 1) {
            *share *= l;
          }
        }
        share
      }

      share_ciphertext_openings.insert(
        participant,
        Zeroizing::new((
          UnsignedInteger::random(class_group.unknown_order_bound() + 128, &mut *rng),
          *polynomial(&coeffs, participant),
        )),
      );
    }

    // Calculate the share ciphertexts
    let share_ciphertexts = share_ciphertext_openings
      .iter()
      .map(|(participant, mask_and_scalar)| {
        let (mask, scalar) = &**mask_and_scalar;
        (*participant, {
          let mask = Zeroizing::new(mask.to_be_bytes());
          CG::multiexp(
            class_group.identity_p(),
            &[(&G, &mask), (class_group.f(), &Zeroizing::new(crate::be_bytes(scalar)))],
          )
        })
      })
      .collect();

    // Create the view
    let view = Arc::new(SetupView::new_internal(
      t,
      class_group_seed,
      security_level,
      verification_key,
      share_ciphertexts,
    ));

    // Create each participant's setup
    let mut res = HashMap::new();
    for i in (1 ..= n).map(|i| Participant::new(i).unwrap()) {
      res.insert(
        i,
        Arc::new(Setup {
          view: view.clone(),
          i,
          share_ciphertext_opening: share_ciphertext_openings.remove(&i).unwrap(),
        }),
      );
    }
    Some(res)
  }
}
