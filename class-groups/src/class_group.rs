use core::marker::PhantomData;

use rand::CryptoRng;

use crate::{Table, ElementExt, NegativeDiscriminant as _, Cl15p};

use ::crypto_bigint::{Odd, Encoding as _, BoxedUint};
/// A class group.
#[derive(Clone)]
pub struct ClassGroup<E: ElementExt> {
  cl15p: Cl15p<BoxedUint, BoxedUint, BoxedUint, BoxedUint>,
  f_table: Table<E>,
  _E: PhantomData<E>,
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
  #[must_use]
  pub fn setup(rng: &mut impl CryptoRng, lambda: u64, p_le_bytes: Vec<u8>) -> Option<Self> {
    Cl15p::sample(
      rng,
      4,
      u32::try_from(2 * lambda).unwrap(),
      Odd::new(BoxedUint::from_le_bytes(p_le_bytes.into())).unwrap(),
    )
    .ok()
    .map(|cl15p| {
      let identity = E::identity(cl15p.absolute_value());
      let f = cl15p.f();
      Self { cl15p, f_table: Table::new(12, identity, f), _E: PhantomData }
    })
  }

  /// The prime-order of the subgroup where the discrete log problem is easy.
  #[must_use]
  pub fn p(&self) -> impl AsRef<[u8]> {
    self.cl15p.fundamental_discriminant().p().to_be_bytes()
  }

  /// The bound on the unknown order, in bits.
  ///
  /// Scalars for the unknown-order should be sampled from this bound plus a further `k`-bits
  /// representing the desired `2**-k` distance from this bound upon sampling.
  #[must_use]
  pub fn unknown_order_bound(&self) -> u32 {
    self.cl15p.upper_bound_on_order()
  }

  /// The identity element for the discriminant `p`.
  #[must_use]
  pub fn identity_p(&self) -> E {
    E::identity(self.cl15p.absolute_value())
  }

  /// Obtain a generator of the squares of the class group with discriminant `p`.
  ///
  /// This function executes in variable time.
  #[cfg(feature = "alloc")]
  #[must_use]
  pub fn generator_p(&self, rng: &mut impl CryptoRng) -> E {
    use ::crypto_bigint::{NonZero, RandomMod as _, BoxedUint};
    let discriminant_abs = self.delta_p();
    let discriminant_abs = discriminant_abs.as_ref();
    let seed = BoxedUint::random_mod_vartime(
      rng,
      &NonZero::new(
        BoxedUint::from_le_slice_vartime(discriminant_abs).wrapping_shr_vartime(2).floor_sqrt(),
      )
      .unwrap(),
    );
    E::next_prime_ideal_squared(rng, seed, discriminant_abs, 128)
  }

  /// The generator for the known-order subgroup over discriminant `p`.
  #[must_use]
  pub fn f(&self) -> &Table<E> {
    &self.f_table
  }

  /// Solve for the discrete logarithm of an element in the class group of discriminant `p`.
  ///
  /// This function executes in variable time.
  #[must_use]
  pub fn discrete_logarithm(&self, X: &E) -> Option<Vec<u8>> {
    Option::<BoxedUint>::from(self.cl15p.discrete_logarithm(X.clone()))
      .map(|up| up.to_be_bytes().to_vec())
  }

  /// The little-endian encoding of the non-fundamental discriminant.
  #[must_use]
  pub fn delta_p(&self) -> impl AsRef<[u8]> {
    self.cl15p.absolute_value()
  }
}

#[cfg(test)]
fn test_class_group<E: ElementExt>(mut rng: impl CryptoRng) {
  let prime = 19;
  let cg = ClassGroup::<E>::setup(&mut rng, 100, vec![prime]).unwrap();

  // Do some complete-ness tests regarding identity
  assert_eq!(cg.identity_p().double(), cg.identity_p());
  assert_eq!(cg.identity_p().add(&cg.identity_p()), cg.identity_p());
  assert_eq!(-cg.identity_p(), cg.identity_p());

  // Select a generator
  let g = cg.generator_p(&mut rng);
  assert_ne!(g, cg.identity_p());
  let g = Table::new(10, cg.identity_p(), g);

  // Check add is complete with regards to doubling
  assert_eq!(g[1].add(&g[1]), g[1].double());
  // Check add is complete with regards to additive inverses
  assert_eq!(g[1].add(&-g[1].clone()), cg.identity_p());

  // Check the table is correctly populated
  {
    assert_ne!(g[1], cg.identity_p());
    let mut d = cg.identity_p();
    for (i, e) in g.as_ref().iter().enumerate() {
      assert_eq!(&d, e, "{i}");
      d = d.add(&g[1]);
    }
  }

  // Check mul is sane
  {
    let mut res = cg.identity_p();
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
  assert_eq!(E::mul(cg.f(), &[prime]), cg.identity_p());

  // Check we can solve for the discrete logarithm of all of our tabled scalings of f
  for (i, f) in cg.f().as_ref().iter().enumerate() {
    let mut i = u32::try_from(i % usize::from(prime)).unwrap().to_le_bytes().to_vec();
    while i.last() == Some(&0) {
      i.pop();
    }
    let mut logarithm = cg.discrete_logarithm(f);
    if let Some(logarithm) = &mut logarithm {
      while logarithm.first() == Some(&0) {
        logarithm.remove(0);
      }
    }
    assert_eq!(logarithm, Some(i));
  }

  // Check we can compress identity, which is an instance of the `a == b` exceptional
  {
    let mut bytes = vec![];
    cg.identity_p().compress(&mut bytes).unwrap();
    assert_eq!(E::decompress(&mut bytes.as_slice(), cg.delta_p()).unwrap(), cg.identity_p());
  }

  // Check we can compress all elements of the g table
  for g in g.as_ref() {
    let mut bytes = vec![];
    g.clone().compress(&mut bytes).unwrap();
    assert_eq!(&E::decompress(&mut bytes.as_slice(), cg.delta_p()).unwrap(), g);

    assert_eq!(&E::uncompressed_decode(g.uncompressed_encode(), cg.delta_p()).unwrap(), g);
  }

  // Check we can compress all elements of the f table
  for (i, f) in cg.f().as_ref().iter().enumerate() {
    if (i % usize::from(prime)) == 0 {
      assert_eq!(f, &cg.identity_p());
    }
    let mut bytes = vec![];
    f.clone().compress(&mut bytes).unwrap();
    assert_eq!(&E::decompress(&mut bytes.as_slice(), cg.delta_p()).unwrap(), f);

    assert_eq!(&E::uncompressed_decode(f.uncompressed_encode(), cg.delta_p()).unwrap(), f);
  }

  // Test the coset labelling function
  let label = cg.cl15p.coset_labeling_function::<E>(g[1].clone());
  assert_eq!(label, cg.cl15p.coset_labeling_function::<E>(g[1].add(&cg.f()[1])));
  let dlog = cg.discrete_logarithm(&(label.sub(g[1].clone()))).unwrap();
  assert_eq!(E::mul(cg.f(), &dlog), label.sub(g[1].clone()));
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
#[test]
fn crypto_bigint_stack_class_group() {
  test_class_group::<
    crate::CryptoBigintElement<
      ::crypto_bigint::Uint<{ crypto_bigint::nlimbs(256u32.div_ceil(2)) }>,
    >,
  >(&mut rand::rand_core::UnwrapErr(rand::rngs::SysRng));
}
#[test]
fn crypto_bigint_heap_class_group() {
  test_class_group::<crate::CryptoBigintElement<::crypto_bigint::BoxedUint>>(
    &mut rand::rand_core::UnwrapErr(rand::rngs::SysRng),
  );
}

#[test]
fn bench() {
  use rand::SeedableRng as _;
  use rand_chacha::ChaCha20Rng;
  const SEED: [u8; 32] = [0; 32];
  bench_class_group::<crate::MalachiteElement>(ChaCha20Rng::from_seed(SEED));
  bench_class_group::<
    crate::CryptoBigintElement<
      ::crypto_bigint::Uint<{ crypto_bigint::nlimbs((2560u32 + 2).div_ceil(2)) }>,
    >,
  >(ChaCha20Rng::from_seed(SEED));
  bench_class_group::<crate::CryptoBigintElement<::crypto_bigint::BoxedUint>>(
    ChaCha20Rng::from_seed(SEED),
  );
}
