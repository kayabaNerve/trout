//! Test the signing protocol.

use rand::{rand_core, rngs::SysRng};
use two_round_ecdsa::{Participant, SecurityLevel, Setup, SigningProtocol, Ready};

#[test]
fn sign() {
  type ProverElement = class_groups::CryptoBigintElement<
    crypto_bigint::Uint<{ crypto_bigint::nlimbs(2048u32.div_ceil(2)) }>,
  >;
  type Element = class_groups::MalachiteElement;
  type Primes = two_round_ecdsa::proofs::CryptoPrimesStackCcykc;

  let mut setups = Setup::<ProverElement, Element, two_round_ecdsa::Secp256k1<Primes>>::dealer(
    &mut rand_core::UnwrapErr(SysRng),
    SecurityLevel::Insecure,
    2,
    3,
  )
  .unwrap();
  println!("Setup!");

  let first_i = Participant::new(1).unwrap();
  let first = setups.remove(&first_i).unwrap();
  let second_i = Participant::new(3).unwrap();
  let second = setups.remove(&second_i).unwrap();

  let (first, first_message) =
    SigningProtocol::<_, _, two_round_ecdsa::Secp256k1<Primes>>::participate(
      &mut rand_core::UnwrapErr(SysRng),
      first,
    );
  let (second, second_message) =
    SigningProtocol::<_, _, two_round_ecdsa::Secp256k1<Primes>>::participate(
      &mut rand_core::UnwrapErr(SysRng),
      second,
    );
  println!("Participated!");

  let Ready::Ready(first) =
    first.accumulate(&mut rand_core::UnwrapErr(SysRng), second_i, second_message)
  else {
    panic!()
  };
  let Ready::Ready(second) =
    second.accumulate(&mut rand_core::UnwrapErr(SysRng), first_i, first_message)
  else {
    panic!()
  };
  println!("Accumulated!");

  const MESSAGE: &[u8] = b"Hello, World!";
  let (first, first_message) = first.sign(&mut rand_core::UnwrapErr(SysRng), MESSAGE);
  let (second, second_message) = second.sign(&mut rand_core::UnwrapErr(SysRng), MESSAGE);
  println!("Signed!");

  let Ready::Ready(first_signature) =
    first.aggregate(&mut rand_core::UnwrapErr(SysRng), second_i, second_message)
  else {
    panic!()
  };
  let Ready::Ready(second_signature) =
    second.aggregate(&mut rand_core::UnwrapErr(SysRng), first_i, first_message)
  else {
    panic!()
  };
  let first_signature = first_signature.unwrap();
  let second_signature = second_signature.unwrap();
  assert_eq!(first_signature, second_signature);
  println!("Aggregated!");

  {
    use ecdsa::signature::Verifier as _;
    ecdsa::VerifyingKey::<k256::Secp256k1>::from_affine(
      setups.values().next().unwrap().view().verification_key().to_affine(),
    )
    .unwrap()
    .verify(
      MESSAGE,
      &ecdsa::Signature::from_scalars(first_signature.r(), {
        // Use a normalized `s` since the ECDSA crate rejects non-normalized signature
        let s = first_signature.s();
        if bool::from(k256::elliptic_curve::scalar::IsHigh::is_high(&s)) { -s } else { s }
      })
      .unwrap(),
    )
    .unwrap();
  }
}
