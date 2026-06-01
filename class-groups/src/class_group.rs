use core::cmp::Ordering;
use std::io;

use rand::CryptoRng;

use ::malachite::{
  base::num::{arithmetic::traits::*, basic::traits::*, logic::traits::*},
  *,
};

use crate::{
  *,
  malachite::{natural_from_bytes, natural_to_bytes},
};

// https://eprint.iacr.org/2015/047 B.2 provides this formula
fn c(a: &Natural, b: &Natural, discriminant: &Integer) -> Option<Natural> {
  // b**2 - 4ac = discriminant
  /*
    Since a and b are positive for reduced elements, and our discriminants are negative, c must
    be positive as else we'd have a positive discriminant.
  */
  debug_assert_eq!(discriminant.sign(), Ordering::Less);
  // We solve for c by rewriting as b**2 - discriminant = 4ac, then dividing by 4a.
  let four_ac: Integer = Integer::from(b.pow(2u64)) - discriminant;
  if (&four_ac & Integer::from(3u8)) != Natural::ZERO {
    None?
  }
  let ac = four_ac >> 2u8;
  let (res, rem) = ac.div_rem(Integer::from(a.clone()));
  if rem != Natural::ZERO {
    None?
  }
  Some(res.try_into().unwrap())
}

fn element<E: Element>(a: Natural, b: Integer, discriminant: &Integer) -> E {
  assert_eq!(discriminant.sign(), Ordering::Less, "discriminant wasn't negative");
  assert_eq!(
    discriminant.unsigned_abs_ref() % Natural::from(2u8),
    Natural::ONE,
    "discriminant wasn't odd"
  );

  // `b^2 - 4ac = -|delta|, b^2 + |delta| = 4ac`
  let c = b.unsigned_abs_ref().square() + discriminant.unsigned_abs_ref();
  assert_eq!(c.clone() % Natural::from(4u8), Natural::ZERO);
  let c = c >> 2u32;
  let (c, zero) = c.div_rem(&a);
  assert_eq!(zero, Natural::ZERO);

  assert_eq!(
    a.clone().gcd(b.unsigned_abs_ref().gcd(&c)),
    Natural::ONE,
    "discriminant wasn't primitive"
  );

  E::from(MalachiteElement::reduce(Integer::from(a), b, Integer::from(c), {
    let tess_root = discriminant.unsigned_abs_ref().ceiling_root(4);
    Integer::from(tess_root)
  }))
}

#[must_use]
fn make_coprime(
  mut a: Natural,
  mut b: Integer,
  prime: &Natural,
  delta: &Integer,
) -> (Natural, Integer) {
  #[cfg(debug_assertions)]
  let original_a = a.clone();
  #[cfg(debug_assertions)]
  let original_b = b.clone();

  let mut c = Integer::from(c(&a, b.unsigned_abs_ref(), delta).unwrap());

  // (a, b, c) -> (a + b + c, -b - 2a, a)
  while !(&a).coprime_with(prime) {
    let int_abc = Integer::from(&a) + &b + &c;
    c = Integer::from(&a);
    b = -b;
    b -= Integer::from(&a << 1);
    a = int_abc.unsigned_abs();
  }

  #[cfg(debug_assertions)]
  {
    debug_assert_eq!(
      {
        let reduced = MalachiteElement::reduce(Integer::from(a.clone()), b.clone(), c.clone(), {
          let delta = b.clone().square() - ((Integer::from(a.clone()) * c.clone()) << 2u32);
          let tess_root = delta.unsigned_abs_ref().ceiling_root(4);
          Integer::from(tess_root)
        });
        // SAFETY: `a_b_c_discriminant` is always safe to call
        let (a, (b_positive, b), _c, _discriminant) = unsafe { reduced.a_b_c_discriminant() };
        let mut b = Integer::from(natural_from_bytes(b.as_ref()));
        if !bool::from(b_positive) {
          b = -b;
        }
        (natural_from_bytes(a.as_ref()), b)
      },
      (original_a, original_b)
    );
  }

  (a, b)
}

/// A class group.
#[derive(Clone)]
pub struct ClassGroup<E: ElementExt> {
  B: Natural,
  p: Natural,
  p_le_bytes: Vec<u8>,
  // TODO identity_k: E,
  identity_p: E,
  f_table: Table<E>,
  delta_k: Integer,
  delta_p: Integer,
}
impl<E: ElementExt> ClassGroup<E> {
  /// Perform the setup for a randomly sampled class group with a subgroup where the discrete
  /// logarithm is easy.
  ///
  /// This function runs in variable time.
  ///
  /// `2 lambda` will the bit-length of the fundamental discriminant. 1827 is suggested as the
  /// bit-length of the fundamental discriminant for 128-bit security but please review
  /// <https://eprint.iacr.org/2020/196> for context on choices.
  ///
  /// `p_le_bytes` is expected to be the little-endian encoding of the odd prime order of the
  /// subgroup.
  // https://eprint.iacr.org/2015/047 Figure 2, slightly modified with regards to `g`
  pub fn setup(rng: &mut impl CryptoRng, lambda: u64, p_le_bytes: Vec<u8>) -> Option<Self> {
    let p = natural_from_bytes(&p_le_bytes);

    let mu = p.significant_bits();

    // Step 1
    if lambda < (mu + 2) {
      None?;
    }

    // Step 2
    let q = {
      let q_bits = (2 * lambda) - mu;
      let q_bits = u32::try_from(q_bits).unwrap();
      loop {
        let mut seed = vec![0; usize::try_from(q_bits).unwrap().div_ceil(8)];
        rng.fill_bytes(&mut seed);
        if (q_bits % 8) != 0 {
          let high_bit = 1 << ((q_bits % 8) - 1);
          // Ensure the high bit is set
          seed[0] |= high_bit;
          // Mask off any higher bits
          seed[0] &= (high_bit << 1) - 1;
        }
        let q = super::primes::next_prime(
          &mut *rng,
          seed,
          ({
            let kappa = u32::try_from((8 * p_le_bytes.len()) / 2).unwrap();
            let mut closest_power_of_two = 1u32;
            while (2 * closest_power_of_two) < kappa {
              closest_power_of_two <<= 1;
            }

            // $closest_power_of_two < kappa \le (2 * closest_power_of_two)$
            if kappa.abs_diff(closest_power_of_two) >= kappa.abs_diff(closest_power_of_two << 1) {
              closest_power_of_two <<= 1;
            }
            closest_power_of_two
          })
          .max(128),
        );
        let q = natural_from_bytes(q.to_le_bytes().as_ref());
        debug_assert!((q.significant_bits() - u64::from(q_bits)) < 1);
        // p * q is congruent to -1 mod 4
        if ((&p * &q) & Natural::from(3u8)) != 3u8 {
          continue;
        }
        // jacobi of p/q = -1
        let res = p.clone().jacobi_symbol(&q);
        if res != -1 {
          continue;
        }
        break q;
      }
    };

    // Step 3
    let delta_k = -Integer::from(&p * &q);

    let p_square = p.clone().pow(2u64);
    let delta_p = &delta_k * Integer::from(p_square.clone());

    let identity_p = element::<E>(Natural::ONE, Integer::ONE, &delta_p);

    // Step 4
    let f = {
      let a = p_square.clone();
      let b = p.clone();
      element::<E>(a, Integer::from(b), &delta_p)
    };

    let B = {
      let abs_delta_k: Natural = delta_k.clone().abs().try_into().unwrap();
      let abs_delta_k_cubed = abs_delta_k.pow(3u64);
      let mut quad_root = abs_delta_k_cubed.clone().floor_root(4);
      debug_assert!(quad_root.clone().pow(4u64) < abs_delta_k_cubed);
      // Transform to ceil root
      quad_root += Natural::ONE;
      debug_assert!(quad_root.clone().pow(4u64) >= abs_delta_k_cubed);
      quad_root
    };

    Some(ClassGroup {
      B,
      p_le_bytes,
      p,
      identity_p: identity_p.clone(),
      // Make a very large table for this as it's static to the setup
      // This should be ~24 MB
      f_table: Table::new(12, identity_p, f),
      delta_k,
      delta_p,
    })
  }

  /// The prime-order of the subgroup where the discrete log problem is easy.
  pub fn p(&self) -> impl AsRef<[u8]> {
    self.p_le_bytes.iter().copied().rev().collect::<Vec<_>>()
  }

  /// The bound on the unknown order, in bits.
  ///
  /// Scalars for the unknown-order should be sampled from this bound plus a further `k`-bits
  /// representing the desired `2**-k` distance from this bound upon sampling.
  pub fn unknown_order_bound(&self) -> u32 {
    self.B.significant_bits().try_into().unwrap()
  }

  /// The identity element for the discriminant `p`.
  pub fn identity_p(&self) -> &E {
    &self.identity_p
  }

  /// Obtain a generator of the class group with discriminant `p`.
  ///
  /// This function executes in variable time.
  ///
  /// This uses Wesolowski's hash-to-class-group internally, making it somewhat slow. More
  /// efficient algorithms should be used by the caller if this will be called on a regular basis.
  pub fn generator_p(&self, rng: &mut impl CryptoRng) -> E {
    let prime_limit: Natural = self.delta_p.unsigned_abs_ref().floor_sqrt() >> 1;
    let r = loop {
      let r_bits = u32::try_from(prime_limit.significant_bits()).unwrap();
      let mut seed = vec![0; usize::try_from(r_bits).unwrap().div_ceil(8)];
      rng.fill_bytes(&mut seed);
      if (r_bits % 8) != 0 {
        let high_bit = 1 << ((r_bits % 8) - 1);
        // Ensure the high bit is set
        // TODO: This does make this somewhat non-uniform
        seed[0] |= high_bit;
        // Mask off any bits higher than the square root
        seed[0] &= (high_bit << 1) - 1;
      }
      let r = super::primes::next_prime(&mut *rng, seed, 128);

      let r = natural_from_bytes(r.to_le_bytes().as_ref());
      if r >= prime_limit {
        continue;
      }
      debug_assert_eq!(u64::from(r_bits), r.significant_bits());
      // Select `r` where `r` is congruent to 3 mod 4 to simplify the sqrt calculation
      // This does bias the choice of `r` by a couple of bits
      if (&r % Natural::from(4u8)) != 3u8 {
        continue;
      }
      // Ensure `delta_p` has a square root mod `r`
      if self.delta_p.clone().jacobi_symbol(Integer::from(r.clone())) != 1 {
        continue;
      }
      break r;
    };

    let a = r.clone();
    let b_square = &r - (self.delta_p.unsigned_abs_ref() % &r);
    // The exponent to raise `b_square` to to calculate its square root modulo `r`
    let b_exp = (&r + Natural::from(1u8)) >> 2;
    let mut b = b_square.clone().mod_pow(&b_exp, &r);
    // `b` must be the odd root for there to be a `c`
    if !b.odd() {
      b = &r - b;
    }
    debug_assert_eq!((&b * &b) % &r, b_square);
    // But it is our choice of `b` or `-b`
    let mut b = Integer::from(b);
    if (rng.next_u64() % 2) == 1 {
      b = -b;
    }
    element::<E>(a, b, &self.delta_p)
  }

  /// The generator for the known-order subgroup over discriminant `p`.
  pub fn f(&self) -> &Table<E> {
    &self.f_table
  }

  /// Solve for the discrete logarithm of an element in the class group of discriminant `p`.
  ///
  /// This function executes in variable time.
  ///
  /// This is well-defined for elements which have a discrete logarithm over `f`. This is undefined
  /// for elements which don't have such a discrete logarithm. The caller is expected to check
  /// `d * f == X`, where `d` is the returned discrete-logarithm, to learn if this is well-defined.
  //
  // This method doesn't perform that check itself as the caller may already know the element is
  // well-defined. There's no reason to perform the consistency check, which is non-trivial, in
  // that case.
  pub fn discrete_logarithm(&self, X: &E) -> Option<Vec<u8>> {
    if X == &self.identity_p {
      return Some(vec![]);
    }

    let p = &self.p;
    let p_int = Integer::from(p.clone());

    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (_a, (b_sign, b_value), _c, _discriminant) = unsafe { X.a_b_c_discriminant() };
    let mut b_value = Integer::from(natural_from_bytes(b_value.as_ref()));
    if !bool::from(b_sign) {
      b_value = -b_value;
    }

    let mut x = (&b_value / &p_int) % &p_int;
    if x.sign() == Ordering::Less {
      x = p_int + x;
    }
    let x = Natural::try_from(x).unwrap();
    if x == Natural::ZERO {
      None?
    }
    let inverse = x.clone().mod_pow(&(p - Natural::from(2u8)), p);
    debug_assert_eq!(((&inverse * &x) % p), Natural::ONE);
    Some(natural_to_bytes(&inverse))
  }

  /// Decompress an element in the class group of discriminant `p`.
  ///
  /// This function executes in variable time.
  pub fn decompress_p(&self, reader: impl io::Read) -> io::Result<E> {
    E::decompress(reader, natural_to_bytes(self.delta_p.unsigned_abs_ref()))
  }

  /// Map an element of the class group with discriminant `k` with a distinct type into this
  /// element type.
  ///
  /// This has undefined behavior for an element which isn't of discriminant `k`.
  ///
  /// This function executes in variable time.
  pub fn map_k<E2: Element>(&self, e: &E2) -> E {
    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b), _c, _discriminant) = unsafe { e.a_b_c_discriminant() };
    let mut b = Integer::from(natural_from_bytes(b.as_ref()));
    if !bool::from(b_positive) {
      b = -b;
    }
    // `unwrap` is fine as this is either valid or of a different discriminant, which means we're
    // allowed to have undefined behavior
    element::<E>(natural_from_bytes(a.as_ref()), b, &self.delta_k)
  }

  /// Map an element of the class group with discriminant `p` with a distinct type into this
  /// element type.
  ///
  /// This has undefined behavior for an element which isn't of discriminant `p`.
  ///
  /// This function executes in variable time.
  pub fn map_p<E2: Element>(&self, e: &E2) -> E {
    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b), _c, _discriminant) = unsafe { e.a_b_c_discriminant() };
    let mut b = Integer::from(natural_from_bytes(b.as_ref()));
    if !bool::from(b_positive) {
      b = -b;
    }
    // `unwrap` is fine as this is either valid or of a different discriminant, which means we're
    // allowed to have undefined behavior
    element::<E>(natural_from_bytes(a.as_ref()), b, &self.delta_p)
  }

  /// Surject an element of the class group of discriminant `p` to the class group of discriminant
  /// `k`.
  ///
  /// This has undefined behavior for an element which isn't of discriminant `p`.
  ///
  /// This function executes in variable time.
  // HJPT98, Algorithm 3, for odd discriminants (b_O = 1)
  pub fn surject(&self, e: &E) -> E {
    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b), _c, _discriminant) = unsafe { e.a_b_c_discriminant() };
    let a = natural_from_bytes(a.as_ref());
    let mut b = Integer::from(natural_from_bytes(b.as_ref()));
    if !bool::from(b_positive) {
      b = -b;
    }

    // Ensure `a` and `p` are coprime
    let (a, mut b) = make_coprime(a, b, &self.p, &self.delta_p);

    // Apply the surjections
    let (_one, mu, lambda) = (&self.p).extended_gcd(&a);
    b = (b * mu) + (Integer::from(&a) * lambda);

    let c = Integer::from(c(&a, b.unsigned_abs_ref(), &self.delta_k).unwrap());
    self.map_k(&MalachiteElement::reduce(Integer::from(a), b, c, {
      let tess_root = self.delta_k.unsigned_abs_ref().ceiling_root(4);
      Integer::from(tess_root)
    }))
  }

  /// Inject an element of the class group of discriminant `k` to the class group of discriminant
  /// `p`.
  ///
  /// This has undefined behavior for an element which isn't of discriminant `k`.
  ///
  /// This function executes in variable time.
  // HJPT, Algorithm 2
  pub fn inject(&self, e: E) -> E {
    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b), _c, _discriminant) = unsafe { e.a_b_c_discriminant() };
    let a = natural_from_bytes(a.as_ref());
    let mut b = Integer::from(natural_from_bytes(b.as_ref()));
    if !bool::from(b_positive) {
      b = -b;
    }

    // Ensure `a` and `p` are coprime
    let (a, mut b) = make_coprime(a, b, &self.p, &self.delta_k);

    // Apply the injection
    b *= Integer::from(&self.p);
    let c = Integer::from(c(&a, b.unsigned_abs_ref(), &self.delta_p).unwrap());

    self.map_p(&MalachiteElement::reduce(Integer::from(a), b, c, {
      let tess_root = self.delta_p.unsigned_abs_ref().ceiling_root(4);
      Integer::from(tess_root)
    }))
  }

  /// Apply the coset labelling function for an element in the class group of discriminant `p`.
  ///
  /// This has undefined behavior for an element which isn't of discriminant `p`.
  ///
  /// This function executes in variable time.
  pub fn coset_labelling_function(&self, e: &E) -> E {
    self.inject(self.surject(e))
  }
}

#[cfg(test)]
fn test_class_group<E: ElementExt>(mut rng: impl CryptoRng) {
  let prime = 19;
  let cg = ClassGroup::<E>::setup(&mut rng, 100, vec![prime]).unwrap();

  // Do some complete-ness tests regarding identity
  assert_eq!(&cg.identity_p.double(), &cg.identity_p);
  assert_eq!(&cg.identity_p.add(&cg.identity_p), &cg.identity_p);
  assert_eq!(&-cg.identity_p.clone(), &cg.identity_p);

  // Select a generator
  let g = cg.generator_p(&mut rng);
  assert_ne!(g, cg.identity_p);
  let g = Table::new(10, cg.identity_p.clone(), g);

  // Check add is complete with regards to doubling
  assert_eq!(g[1].add(&g[1]), g[1].double());
  // Check add is complete with regards to additive inverses
  assert_eq!(g[1].add(&-g[1].clone()), cg.identity_p);

  // Check the table is correctly populated
  {
    assert!(g[1] != cg.identity_p);
    let mut d = cg.identity_p.clone();
    for (i, e) in g.as_ref().iter().enumerate() {
      assert_eq!(&d, e, "{i}");
      d = d.add(&g[1]);
    }
  }

  // Check mul is sane
  {
    let mut res = cg.identity_p.clone();
    res = res.add(&g[1].double());
    assert_eq!(res, E::mul(&g, &[2]));

    let mut pow = g[255].clone().add(&g[1]);
    res = res.add(&pow);
    assert_eq!(res, E::mul(&g, &[1, 2]));
    for _ in 0 .. 8 {
      pow = pow.double();
    }
    res = res.add(&pow);
    assert_eq!(res, E::mul(&g, &[1, 1, 2]));
    for _ in 0 .. 8 {
      pow = pow.add(&pow);
    }
    res = res.add(&pow);
    assert_eq!(res, E::mul(&g, &[1, 1, 1, 2]));
  }

  // Check f * prime == identity
  assert_eq!(E::mul(&cg.f_table, &[prime]), cg.identity_p);

  // Check we can solve for the discrete logarithm of all of our tabled scalings of f
  for (i, f) in cg.f().as_ref().iter().enumerate() {
    let mut i = u32::try_from(i % usize::from(prime)).unwrap().to_le_bytes().to_vec();
    while i.last() == Some(&0) {
      i.pop();
    }
    assert_eq!(cg.discrete_logarithm(f), Some(i));
  }

  // Check we can compress identity, which is an instance of the `a == b` exceptional
  {
    let mut bytes = vec![];
    cg.identity_p.compress(&mut bytes).unwrap();
    assert_eq!(&cg.decompress_p(&mut bytes.as_slice()).unwrap(), &cg.identity_p);
  }

  // `b == 0` is another exceptional case, yet given `b**2 - 4ac = delta_p`, this would simplify to
  // `-4ac = delta_p`. Since our discriminants are not divisible by `4`, there is no `ac` (even
  // unreduced) which would cause this exceptional case to be triggered.
  assert!(cg.delta_p.clone().div_rem(Integer::from(4i8)).1 != Integer::ZERO);

  // Check we can compress all elements of the g table
  for g in g.as_ref() {
    let mut bytes = vec![];
    g.compress(&mut bytes).unwrap();
    assert_eq!(&cg.decompress_p(&mut bytes.as_slice()).unwrap(), g);
  }

  // Check we can compress all elements of the f table
  for (i, f) in cg.f_table.as_ref().iter().enumerate() {
    if (i % usize::from(prime)) == 0 {
      assert_eq!(f, &cg.identity_p);
    }
    let mut bytes = vec![];
    f.compress(&mut bytes).unwrap();
    assert_eq!(&cg.decompress_p(&mut bytes.as_slice()).unwrap(), f);
  }

  // Test the coset labelling function
  let label = cg.coset_labelling_function(&g[1]);
  assert_eq!(label, cg.coset_labelling_function(&(g[1].add(&cg.f_table[1]))));
  let dlog = cg.discrete_logarithm(&(label.sub(g[1].clone()))).unwrap();
  assert_eq!(E::mul(&cg.f_table, &dlog), label.sub(g[1].clone()));
}

#[cfg(test)]
fn bench_class_group<E: ElementExt>(mut rng: impl CryptoRng) {
  // Benchmark with the maximum size of class group supported by CryptoBigintStackElement
  let prime = 19u8;
  // The fundamental discriminant is of length `lambda * 2`, yet then that's scaled by `prime**2`
  // `2560`, the target class group size, minus the logarithm of `prime**2`, divided by 2
  let lambda = (2560 - u64::from((u64::from(prime) * u64::from(prime)).ilog2())) / 2;
  let class_group = ClassGroup::<E>::setup(&mut rng, lambda, vec![prime]).unwrap();
  let g = class_group.generator_p(&mut rng);

  {
    let mut element = g.clone();
    let start = std::time::Instant::now();
    const ITERS: u32 = 10000;
    for _ in 0 .. ITERS {
      element = element.double();
    }
    let end = std::time::Instant::now();
    println!(
      "{} took {}ms for {} NUDUPLs",
      core::any::type_name::<E>(),
      end.duration_since(start).as_millis(),
      ITERS
    );
  }

  {
    let mut element = g.clone();
    let start = std::time::Instant::now();
    const ITERS: u32 = 10000;
    for _ in 0 .. ITERS {
      element = element.add(&element);
    }
    let end = std::time::Instant::now();
    println!(
      "{} took {}ms for {} NUCOMPs",
      core::any::type_name::<E>(),
      end.duration_since(start).as_millis(),
      ITERS
    );
  }
}

#[test]
fn malachite_class_group() {
  test_class_group::<crate::MalachiteElement>(&mut rand::rand_core::UnwrapErr(rand::rngs::SysRng));
}
#[expect(deprecated)]
#[test]
fn crypto_bigint_stack_class_group() {
  test_class_group::<crate::CryptoBigintStackElement>(&mut rand::rand_core::UnwrapErr(
    rand::rngs::SysRng,
  ));
}
#[expect(deprecated)]
#[test]
fn crypto_bigint_heap_class_group() {
  test_class_group::<crate::CryptoBigintHeapElement>(&mut rand::rand_core::UnwrapErr(
    rand::rngs::SysRng,
  ));
}
#[cfg(feature = "gmp")]
#[test]
fn gmp_class_group() {
  test_class_group::<crate::GmpElement>(&mut rand::rand_core::UnwrapErr(rand::rngs::SysRng));
}

#[expect(deprecated)]
#[test]
fn bench() {
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  const SEED: [u8; 32] = [0; 32];
  bench_class_group::<crate::MalachiteElement>(ChaCha20Rng::from_seed(SEED));
  bench_class_group::<crate::CryptoBigintStackElement>(ChaCha20Rng::from_seed(SEED));
  bench_class_group::<crate::CryptoBigintHeapElement>(ChaCha20Rng::from_seed(SEED));
  #[cfg(feature = "gmp")]
  bench_class_group::<crate::GmpElement>(ChaCha20Rng::from_seed(SEED));
}
