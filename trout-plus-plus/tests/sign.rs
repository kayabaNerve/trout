//! Test the signing protocol.

use std::{time::Instant, collections::HashMap};

use zeroize::Zeroizing;
use rand::{rand_core, rngs::SysRng};

use p256::elliptic_curve::PrimeField as _;
use ciphersuite::group::{ff::PrimeField as _, GroupEncoding as _};

use crypto_bigint::{U256, U512, BoxedUint};
use trout_plus_plus::{
  WrappedGroup as _, NonInteractiveSetup, InteractiveSetup, Preprocess, Aggregating, Sign, P256,
};

use dkg_dealer::Participant;

#[test]
fn sign() {
  /*
    - 1827 corresponds to 128-bit computational security with 14-bit statistical security
    - 3072 corresponds to 128-bit computational security with 40-bit statistical security
    - 4096 corresponds to 128-bit computational security with 64-bit statistical security
    - 6784 corresponds to 128-bit computational security with 128-bit statistical security

    Trustless unknown-order groups by Samuel Dobson, Steven D. Galbraith, and Benjamin Smith,
    https://eprint.iacr.org/2020/196 Table 2

    We only use 1827 here as a reference point as frequently used for benchmarking works with class
    groups. Per NIST.IR.8214C, 40 bits of statistical security is required for submissions, with
    64 bits preferred, meaning the minimum should be 3072.
  */
  const FUNDAMENTAL_DISCRIMINANT_BIT_LENGTH: u16 = 1827;
  #[expect(clippy::as_conversions)]
  type ProverElement = class_groups::CryptoBigintElement<
    crypto_bigint::Uint<
      {
        crypto_bigint::nlimbs(
          ((FUNDAMENTAL_DISCRIMINANT_BIT_LENGTH as u32) + (2u32 * 256u32)).div_ceil(2),
        )
      },
    >,
  >;
  type VerifierElement = bicycl::BicyclElement;

  let mut rng = rand_core::UnwrapErr(SysRng);

  // Convert from `p256 0.13` (`dkg-dealer`) to a `p256 0.14` (`trout-plus-plus`)
  let scalar_13_14 = |scalar: <ciphersuite_kp256::P256 as ciphersuite::Ciphersuite>::F| {
    p256::Scalar::from_repr(<[u8; 32]>::from(scalar.to_repr()).into()).unwrap()
  };
  let point_13_14 = |point: <ciphersuite_kp256::P256 as ciphersuite::Ciphersuite>::G| {
    P256::point_from_canonical_bytes(&mut <_ as AsRef<[u8]>>::as_ref(&point.to_bytes())).unwrap()
  };

  let keys =
    dkg_dealer::key_gen::<_, ciphersuite_kp256::P256>(&mut rand_core_06::OsRng, 3, 5).unwrap();
  let mut signing_set = vec![
    dkg_dealer::Participant::new(1).unwrap(),
    dkg_dealer::Participant::new(2).unwrap(),
    dkg_dealer::Participant::new(4).unwrap(),
  ];
  // Aggregation, determination of the signing key, requires a definitive ordering
  signing_set.sort_unstable();
  let interpolation_factors = {
    let view = keys[&signing_set[0]].view(signing_set.clone()).unwrap();
    signing_set
      .iter()
      .copied()
      .map(|id| (id, scalar_13_14(view.interpolation_factor(id).unwrap())))
      .collect::<HashMap<_, _>>()
  };

  let non_interactive_setup =
    NonInteractiveSetup::<U256, U512, BoxedUint, BoxedUint>::setup::<P256>(
      &mut rng,
      [keys.values().next().unwrap().group_key().to_bytes()],
      FUNDAMENTAL_DISCRIMINANT_BIT_LENGTH,
    )
    .unwrap();
  println!("NonInteractiveSetup");

  let mut key_ciphertext_openings = HashMap::new();
  let mut setups = HashMap::new();
  for (id, keys) in &keys {
    let mut setup = vec![];
    let (_setup, key_ciphertext_opening) =
      InteractiveSetup::<ProverElement>::setup::<BoxedUint, BoxedUint, P256>(
        &mut rng,
        &non_interactive_setup,
        Zeroizing::new(scalar_13_14(**keys.original_secret_share())),
        &mut setup,
      )
      .unwrap();
    key_ciphertext_openings.insert(id, key_ciphertext_opening);

    let mut setup = setup.as_slice();
    setups.insert(
      id,
      InteractiveSetup::<VerifierElement>::verify::<BoxedUint, BoxedUint, P256>(
        &mut rng,
        &non_interactive_setup,
        point_13_14(keys.original_verification_share(*id)),
        &mut setup,
      )
      .unwrap(),
    );
    assert!(setup.is_empty());
  }
  println!("Setup");

  let mut preprocesses = HashMap::new();
  let mut preprocess_openings = HashMap::new();
  let mut aggregating = signing_set
    .iter()
    .map(|id| {
      (*id, Aggregating::<BoxedUint, BoxedUint, VerifierElement, P256>::new(&non_interactive_setup))
    })
    .collect::<HashMap<_, _>>();
  for id in &signing_set {
    let start = Instant::now();
    let mut encoding = vec![];
    let preprocess_opening = Preprocess::<ProverElement>::participate::<_, _, P256>(
      rng,
      &non_interactive_setup,
      &mut encoding,
    )
    .unwrap();
    preprocess_openings.insert(id, preprocess_opening);
    println!(
      "Preprocessed once in {}ms taking {} bytes",
      start.elapsed().as_millis(),
      encoding.len()
    );

    for aggregating in aggregating.values_mut() {
      let start = Instant::now();
      let mut encoding = encoding.as_slice();
      // Note aggregation is SPECIFIC TO THE ORDER AGGREGATED
      let preprocess = aggregating.aggregate(rng, &mut encoding).unwrap();
      preprocesses.insert(id, preprocess);
      assert!(encoding.is_empty());
      println!("Aggregated once in {}ms", start.elapsed().as_millis());
    }
  }
  println!("Preprocessed");

  let group_key = point_13_14(keys.values().next().unwrap().original_group_key());
  let signing_key = InteractiveSetup::signing_key(
    &non_interactive_setup,
    group_key,
    signing_set.iter().map(|id| (interpolation_factors[id], &setups[id])),
  );
  const MESSAGE: &[u8] = b"Hello, World!";

  let mut completing = None;
  for (id, preprocess_opening) in preprocess_openings {
    let start = Instant::now();
    let aggregating = aggregating.remove(id).unwrap().verify().unwrap();
    println!("Batch verified preprocesses in {}ms", start.elapsed().as_millis());

    let start = Instant::now();
    let preprocess = preprocesses.remove(id).unwrap();
    let mut share = vec![];
    let first = completing.is_none();
    completing = completing.or(Some(
      Sign::sign::<BoxedUint, BoxedUint, ProverElement, VerifierElement, _, P256, _, Participant>(
        &mut rng,
        &non_interactive_setup,
        &signing_key,
        interpolation_factors[id],
        setups[id].clone(),
        key_ciphertext_openings[id].clone(),
        aggregating,
        &preprocess,
        preprocess_opening,
        MESSAGE,
        &mut share,
      )
      .unwrap(),
    ));
    println!("Signed share once in {}ms taking {} bytes", start.elapsed().as_millis(), share.len());

    if !first {
      let start = Instant::now();
      let completing = completing.as_mut().unwrap();
      let mut share = share.as_slice();
      completing
        .aggregate(rng, *id, interpolation_factors[id], setups[id].clone(), preprocess, &mut share)
        .unwrap();
      assert!(share.is_empty());
      println!("Aggregated share in {}ms", start.elapsed().as_millis());
    }
  }

  let start = Instant::now();
  let signature = completing.unwrap().complete().unwrap();
  println!("Recovered signature in {}ms", start.elapsed().as_millis());

  {
    use ecdsa::signature::Verifier as _;
    let () = ecdsa::VerifyingKey::<p256::NistP256>::from_affine(group_key.to_affine())
      .unwrap()
      .verify(MESSAGE, &ecdsa::Signature::from_scalars(signature.r, signature.s).unwrap())
      .unwrap();
  }
}
