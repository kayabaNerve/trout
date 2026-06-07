//! Benchmark how long sampling primes takes.

#[test]
fn primes() {
  use trout_plus_plus::proofs::{Primes, CryptoPrimesStack, CryptoPrimesHeap};

  fn test<P: Primes>() {
    let start = std::time::Instant::now();
    for _ in 0 .. 10000 {
      let _prime = core::hint::black_box(P::prime(128, blake3::Hasher::new().finalize_xof()));
    }
    let end = std::time::Instant::now();
    println!(
      "{} 1000 128-bit primes: {}",
      core::any::type_name::<P>(),
      end.duration_since(start).as_millis()
    );
  }

  test::<CryptoPrimesStack<crypto_bigint::U128>>();
  test::<CryptoPrimesHeap>();
}
