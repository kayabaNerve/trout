use core::{fmt::Debug, ops::Neg};
#[cfg(feature = "std")]
use std::io;

use crypto_bigint::{Choice, CtOption};

/// A primitive positive definite binary quadratic form of negative odd discriminant (not
/// necessarily fundamental) with `a, b, c` coefficients.
///
/// # Safety
///
/// Implementations MUST return well-defined coefficients for a primitive _reduced_ positive
/// definite binary quadratic form of a negative odd discriminant (the one whose value is
/// yielded). It is undefined behavior to not do so.
pub unsafe trait Coefficients {
  /// Fetch the `a, b, c` coefficients of the single reduced form equivalent to this form and the
  /// absolute value of its negative discriminant.
  ///
  /// The coefficients and absolute value of the discriminant are little-endian encoded.
  /// `b` is represented by a sign bit, if `b` is positive (greater than or equal to zero), and the
  /// encoding of its absolute value. Values MAY have trailing zeroes.
  #[expect(clippy::type_complexity)]
  fn a_b_c_discriminant(
    self,
  ) -> (impl AsRef<[u8]>, (Choice, impl AsRef<[u8]>), impl AsRef<[u8]>, impl AsRef<[u8]>);
}

/// An binary quadratic form corresponding to an element of a class group.
///
/// This binary quadratic form is bound to being a primitive positive definite binary
/// quadratic form of negative odd discriminant (not necessarily fundamental). We bound to
/// primitive forms to ensure forms are invertible and for faster composition. We bound to
/// positive definite (of negative discriminant) forms to ensure there's a single reduced form, and
/// as the theory sufficiently diverges it doesn't make practical sense to attempt to
/// simultaneously support both in a single optimized library. We bound to odd discriminants as
/// specializing enables ~5% faster reduction. Additionally, all of these bounds are allowed by the
/// currently desired use cases.
///
/// This binary quadratic form has a specific discriminant. Operations between binary quadratic
/// forms with distinct discriminants are _always_ undefined behavior (and technically considered
/// `unsafe` even if not so annotated) and MUST NOT be done.
///
/// Operations with the binary quadratic forms are not notated multiplicatively but additively.
/// The composition of two forms is referred to as addition, and the composition of a form with
/// itself is referred to as doubling. The inverse of an element is notated as its negation.
///
/// Implementations of this trait MAY run in variable time.
pub trait Element:
  Sized + Send + Sync + Clone + PartialEq + Eq + Debug + Neg<Output = Self> + Coefficients
{
  /// The identity element.
  ///
  /// The negative discriminant is specified by the little-endian encoding of its absolute value.
  ///
  /// This MUST panic if the discriminant is not a valid odd discriminant.
  fn identity(discriminant_abs: impl AsRef<[u8]>) -> Self;

  /// If this element is the identity.
  fn is_identity(&self) -> Choice;

  /// Double this element.
  ///
  /// This is generally faster than adding an element to itself as it's allowed to specialize on
  /// this special case.
  #[must_use]
  fn double(&self) -> Self;
  /// Add two elements.
  #[must_use]
  fn add(&self, other: &Self) -> Self;
  /// Subtract one element from another.
  #[must_use]
  fn sub(&self, other: Self) -> Self;

  /// Load a form from its coefficients.
  ///
  /// The coefficients and absolute value of the discriminant are little-endian encoded. `b` is
  /// represented by a sign bit, if `b` is positive (greater than or equal to zero), and the
  /// encoding of its absolute value. Values MAY have trailing zeroes.
  ///
  /// # Safety
  ///
  /// The coefficients MUST specify a primitive _reduced_ positive definite binary quadratic form
  /// of negative odd discriminant, the one specified via `discriminant_abs`. Implementations MAY
  /// exhibit undefined behavior if any of these requirements aren't satisfied, hence this being
  /// marked `unsafe`. This MUST NOT be unsafe for any other reason (such as if the coefficients
  /// exceed the type's bounds) but MAY panic if documented bounds on the discriminant aren't met.
  // Currently, all provided implementations will simply be incorrect (and may panic) if these
  // conditions aren't met. The usage of `unsafe` is simply to allow implementations to introduce
  // `unsafe` operations around these preconditions, when all loaded forms should be from
  // (un)compressed encodings which perform validation at time of decode.
  #[must_use]
  unsafe fn from_coefficients(
    a: impl AsRef<[u8]>,
    b: (Choice, impl AsRef<[u8]>),
    c: impl AsRef<[u8]>,
    discriminant_abs: impl AsRef<[u8]>,
  ) -> Self;

  /// Compress an element.
  ///
  /// This MUST implement the defined specification for the compression of binary quadratic forms.
  /// Implementations MUST only error if the underlying IO errors, being error-free themselves.
  /// This allows callers to `unwrap` this result when the underlying IO is known to be error-free
  /// (such as when a `Vec`).
  ///
  /// The provided implementation runs in variable time and MAY panic for absurdly large
  /// coefficients.
  #[cfg(feature = "std")]
  fn compress(self, mut writer: impl io::Write) -> io::Result<()> {
    use crypto_bigint::{NonZero, BoxedUint};

    let (a, (b_positive, b_abs), _c, discriminant_abs) = self.a_b_c_discriminant();
    let a = a.as_ref();
    let b_abs = b_abs.as_ref();
    let discriminant_abs = discriminant_abs.as_ref();

    let a = BoxedUint::from_le_slice_vartime(a);
    let a = NonZero::new(a).expect("`a > 0` when `delta < 0`");

    let b_abs = BoxedUint::from_le_slice_vartime(b_abs);

    let discriminant_abs = BoxedUint::from_le_slice_vartime(discriminant_abs);

    writer.write_all(&crate::crypto_bigint::encode_compressed_binary_quadratic_form(
      a,
      b_positive,
      b_abs,
      &discriminant_abs,
    ))
  }

  /// Decompress an element of the specified discriminant.
  ///
  /// This MUST implement the defined specification for the decompression of binary quadratic
  /// forms. The discriminant MUST be negative and odd, specified by the little-endian encoding of
  /// its absolute value.
  ///
  /// The provided implementation runs in variable time and MAY error for absurdly large
  /// discriminants.
  #[cfg(feature = "std")]
  fn decompress(reader: impl io::Read, discriminant_abs: impl AsRef<[u8]>) -> io::Result<Self> {
    let discriminant_abs = discriminant_abs.as_ref();

    {
      let lsb = discriminant_abs.first().ok_or(io::Error::other("zero-length discriminant"))?;
      if (lsb & 1) != 1 {
        Err(io::Error::other("non-odd discriminant"))?;
      }
    }

    let (a, (b_positive, b_abs), c) =
      crate::crypto_bigint::decode_compressed_binary_quadratic_form(
        reader,
        &::crypto_bigint::BoxedUint::from_le_slice(
          discriminant_abs,
          u32::try_from(8 * discriminant_abs.len())
            .map_err(|_| io::Error::other("absurdly large discriminant?"))?,
        )
        .map_err(|e| {
          io::Error::other(alloc::format!(
            "container overflowed despite precision proportional to length of the encoding: {e:?}"
          ))
        })?,
      )
      .map_err(|e| io::Error::other(alloc::format!("{e:?}")))?;
    let a = a.to_le_bytes();
    let b_abs = b_abs.to_le_bytes();
    let c = c.to_le_bytes();

    /*
      SAFETY: These coefficients must be well-defined for this to be safe, and
      `decode_compressed_binary_quadratic_form` is validated to return a well-defined primitive
      reduced positive definite binary quadratic form of the specified negative discriminant. It
      DOES NOT bound the discriminant to be odd, as we do here, yet this function already checked
      the discriminant is odd.
    */
    Ok(unsafe { Self::from_coefficients(a, (b_positive, b_abs), c, discriminant_abs) })
  }

  /// Encode an element without compression.
  ///
  /// This SHOULD NOT be used by protocols. The compressed encoding SHOULD be used unless there's
  /// an explicit reason to use uncompressed encodings (such as the stronger bounds on termination
  /// or amenability for constant-time implementations).
  ///
  /// This MUST implement the defined specification for the uncompressed encoding of binary
  /// quadratic forms.
  fn uncompressed_encode(&self) -> impl AsRef<[u8]>;

  /// Decode an element of the specified discriminant without compression.
  ///
  /// This SHOULD NOT be used by protocols. The compressed encoding SHOULD be used unless there's
  /// an explicit reason to use uncompressed encodings (such as the stronger bounds on termination
  /// or amenability for constant-time implementations).
  ///
  /// This MUST implement the defined specification for the uncompressed decoding of binary
  /// quadratic forms. The discriminant MUST be negative and odd, specified by the little-endian
  /// encoding of its absolute value. Implementations MUST return `None` if `buf.len()` is not
  /// exactly `2 * ((floor(log_2(-discriminant)) / 2) + 1).div_ceil(8)` OR if the discriminant is
  /// even. Implementations MAY not support discriminants whose absolute values are encoded with
  /// trailing zero bytes.
  fn uncompressed_decode(
    buf: impl AsRef<[u8]>,
    discriminant_abs: impl AsRef<[u8]>,
  ) -> CtOption<Self>;

  /// Create an element of this type from another element.
  fn from(source: impl Element) -> Self {
    let (a, b, c, discriminant) = source.a_b_c_discriminant();
    /*
      SAFETY: These coefficients must be well-defined for this to be safe,
      and `a_b_c_discriminant` is bounded to return well-defined coefficients.

      If we wanted a safe variant, we could instead defer to the uncompressed encoding, but that
      would validate the point on decode to ensure its safety (which is unnecessary for our
      purposes).
    */
    unsafe { Self::from_coefficients(a, b, c, discriminant) }
  }

  /// Sample a uniform element from a subgroup of the class group and return its square.
  ///
  /// The discriminant MUST be negative and is specified by the little-endian encoding of its
  /// absolute value. The discriminant MUST be odd.
  ///
  /// This element is deterministic to the seed, has an unknown relationship to other elements of
  /// the class group, and may be presumed to be a generator of (most of) the squares of the class
  /// group. These properties make this function suitable for use as a hash-to-element for _some_
  /// use cases, and we claim _most_ of the desirable use cases. This function MUST NOT be assumed
  /// to output uniform elements of the class group or to be indistinguishable. The element is
  /// squared as the Decisional Diffie-Hellman problem is easy over the entire class group and it's
  /// its squares which form a generally-desirable subgroup
  /// ("Linearly Homomorphic Encryption from DDH" by Guilhem Castagnos and Fabien Laguillaumie,
  /// <https://eprint.iacr.org/2015/047>, Appendix B.4).
  ///
  /// Implementations MUST implement the specification for sampling a random element of the class
  /// group, as the provided implementation does, with identical results. The provided
  /// implementation executes in variable time and all implementations SHOULD be assumed to execute
  /// in variable time due to the specification only having a statistical bound for its termination
  /// (requiring sampling a prime number).
  ///
  /// "How (not) to hash into class groups of imaginary quadratic fields?", by
  /// István András Seres, Péter Burcsi, and Péter Kutas (<https://eprint.iacr.org/2024/034>), is
  /// referred to as primary academic reference for the analysis and justification of such hash
  /// functions. We specify (and implement) the second construction, attributed to the conference
  /// version of "Efficient verifiable delay functions" by Benjamin Wesolowski, and _not_ the
  /// "Improved version". This is _not_ uniform over the class group as a whole, solely the binary
  /// quadratic forms of prime ideal, assuming the underlying hash-to-prime function is itself
  /// uniform. This is presented as _sufficient_ for most purposes and is remarkably
  /// straightforward to implement, hence it being the reasonable choice for specification.
  ///
  /// ```py
  /// fn next_prime_ideal_squared(seed, discriminant) {
  ///   # Assert the discriminant is negative and sufficiently large there is such a prime ideal
  ///   assert discriminant < -200
  ///   # Assert the seed is within the expected bound
  ///   assert 0 <= seed
  ///   assert seed <= sqrt((-discriminant) / 4)
  ///
  ///   i = 0
  ///   seed = next_odd_prime(seed)
  ///   if seed > sqrt((-discriminant) / 4) {
  ///     # Increment modulo our upper bound to the first odd prime
  ///     seed = 3
  ///   }
  ///   while jacobi(discriminant, seed) != 1 {
  ///     i += 1
  ///     seed = next_odd_prime(seed + 1)
  ///     if seed > sqrt((-discriminant) / 4) {
  ///       seed = 3
  ///     }
  ///   }
  ///
  ///   b = mod_sqrt(delta, p)
  ///   if (i % 2) == 1 {
  ///     b = -b
  ///   }
  ///
  ///   # Return the composition of the sampled prime ideal with itself
  ///   prime_ideal = (p, b)
  ///   return composition(prime_ideal, prime_ideal)
  /// }
  /// ```
  ///
  /// `seed` is required to be a uniform element in the range $[0, sqrt(|discriminant| / 4)]$.
  /// `next_odd_prime` tests if `seed` is an odd prime, incrementing it if it is not, until it is.
  /// `jacobi(x, y)` yields the Jacobi symbol of `x` over `y` where as `y` is an odd prime, this is
  /// equivalent to the Lagrange symbol. `mod_sqrt(x, y)` returns the _odd_ square root of `x`
  /// modulo `y` such that $mod_sqrt(x, y)^2 \cong x \mod y$ if one exists, which our precondition
  /// of checking the Jacobi symbol ensures. `mod_sqrt` is RECOMMENDED to be implemented via the
  /// Tonelli-Shanks algorithms but MAY be implemented with alternatives such as Cipolla's.
  /// `composition` returns the composition (the result of the group operation, the product in
  /// multiplicative notation, the sum in additive notation as this library generally prefers) of
  /// two binary quadratic forms (corresponding to `NUCOMP` or similar, or as the first form is
  /// equal to the second form, `NUDUPL` or similar).
  ///
  /// For the validity of the results, we primarily defer to
  /// "How (not) to hash into class groups of imaginary quadratic fields?" (which did prove this
  /// construction secure and uniform to the prime ideals for primes in the range
  /// $[0, sqrt(|discriminant| / 4)]$). We choose our sign differently from the suggested negative
  /// if $p % 3 = 2$, as for any prime $p$, that would fix a single $b$ coefficient (despite it
  /// naturally having two potential solutions as $|b| < a$). We intead use the amount of rejected
  /// non-residues to decide the sign of $b$, which is uniform modulo `2` if the distribution of
  /// prime quadratic residues to prime quadratic non-residues in a prime field is itself uniform.
  /// The ordinality of the set of non-zero quadratic residues is equivalent to the ordinality of
  /// the set of non-zero quadratic non-residues, so this isn't impossible, though exact analysis
  /// regarding the distribution of primes and the distribution of quadratic non-residues within a
  /// prime field have been open problems with decades (if not centuries, if not millenia) of
  /// literature. Even though we can't prove a tight bound for the bias of this method, we do claim
  /// this method sufficient for our purposes.
  ///
  /// The provided implementation MAY panic upon invalid or absurdly large inputs. It accepts an
  /// RNG to perform primality tests against the prime numbers with though the RNG is not used to
  /// sample potential coefficients for the binary quadratic form and will not impact the result
  /// (except if a primality test fails). `bits_of_security` parameterizes the statistical odds of
  /// a sampled prime number actually being prime. The provided implementation MAY panic if
  /// `bits_of_security` causes there to be no recognized configuration for the Miller-Rabin
  /// primality tests, for the prime numbers considered as candidates.
  #[cfg(feature = "alloc")] // TODO: no-`alloc`
  fn next_prime_ideal_squared(
    mut rng: impl rand::CryptoRng,
    seed: crypto_bigint::BoxedUint,
    discriminant_abs: impl AsRef<[u8]>,
    bits_of_security: u32,
  ) -> Self {
    use crypto_bigint::{CtEq as _, NonZero, Odd, Resize as _, ConcatenatingSquare as _, BoxedUint};
    use crate::crypto_bigint::sqrt_mod_p_vartime;

    let discriminant_abs = discriminant_abs.as_ref();
    assert_eq!(discriminant_abs[0] & 1, 1, "discriminant wasn't odd");
    let discriminant_abs = BoxedUint::from_le_slice_vartime(discriminant_abs);
    // TODO: Confirm this bound is tightly defined
    assert!(discriminant_abs > BoxedUint::from(200u8));
    // As the discriminant is odd, this integer is less than the fractional square root which we
    // have as an exclusive bound
    let inclusive_end = discriminant_abs.wrapping_shr_vartime(2).floor_sqrt();
    assert!(seed <= inclusive_end);
    let mut seed = seed.resize(inclusive_end.bits_precision());
    if seed.bits_vartime() <= 2 {
      seed = BoxedUint::from(3u8).resize(inclusive_end.bits_precision());
    }

    let mut i = 0u64;
    seed = match super::primes::next_prime(&mut rng, seed, bits_of_security) {
      Ok(seed) => seed,
      // Set this past `inclusive_end` so the following code wraps it
      Err(super::primes::Error::Capacity) => inclusive_end.concatenating_add(BoxedUint::one()),
      Err(super::primes::Error::NoMillerRabin) => {
        panic!("bits of security effected no Miller-Rabin configuration")
      }
    };
    if seed > inclusive_end {
      seed = BoxedUint::from(3u8);
    }
    let mut b_abs;
    while {
      let seed = Odd::new(seed.clone()).expect("odd prime wasn't odd?");
      let discriminant_abs_mod_a = discriminant_abs.rem(seed.as_nz_ref());
      let discriminant_mod_a = discriminant_abs_mod_a.neg_mod(seed.as_nz_ref());
      b_abs = sqrt_mod_p_vartime(discriminant_mod_a, &seed);
      b_abs.is_none()
    } {
      i += 1;
      seed = match super::primes::next_prime(
        &mut rng,
        seed.concatenating_add(BoxedUint::one()),
        bits_of_security,
      ) {
        Ok(seed) => seed,
        Err(super::primes::Error::Capacity) => inclusive_end.concatenating_add(BoxedUint::one()),
        Err(super::primes::Error::NoMillerRabin) => {
          panic!("bits of security effected no Miller-Rabin configuration")
        }
      };
      if seed > inclusive_end {
        seed = BoxedUint::from(3u8);
      }
      seed = seed.resize(inclusive_end.bits_precision());
    }

    let (b_positive, b_abs) = {
      let b_abs = b_abs.unwrap();

      #[cfg(debug_assertions)]
      {
        let seed = NonZero::new(seed.clone()).unwrap();
        debug_assert_eq!(
          b_abs.concatenating_square().rem(&seed),
          discriminant_abs.rem(&seed).neg_mod(&seed)
        );
      }

      let b_negative = (i & 1).ct_eq(&1);
      let b_positive = !b_negative;
      (b_positive, b_abs)
    };

    let a = seed;

    // $b^2 - 4ac = -|delta|, b^2 + |delta| = 4ac$ as $delta < 0$
    // TODO: Add a proof on why `b^2 + |delta|` is divisible by `4ac`
    let (four_c, zero) = (b_abs.concatenating_square().concatenating_add(&discriminant_abs))
      .div_rem(&NonZero::new(a.clone()).unwrap());
    assert!(
      bool::from(zero.is_zero()),
      "didn't correctly sample a prime ideal ($b^2 + |delta|$ not divisible by `a`)"
    );
    let (c, zero) = four_c.div_rem(&NonZero::new(BoxedUint::from(4u8)).unwrap());
    assert!(
      bool::from(zero.is_zero()),
      "didn't correctly sample a prime ideal ($(b^2 + |delta|)/a$ not divisible by `4`)"
    );

    let trim = |number: BoxedUint| {
      let mut number = number.to_le_bytes().to_vec();
      while number.last() == Some(&0) {
        number.pop().unwrap();
      }
      number
    };

    /*
      Per Lemma 5.3.4 of A Course in Computational Algebraic Number Theory by Henri Cohen, if
      $a < sqrt(|D| / 4)$ and $-a < b \le a$, then the form is reduced. We bound
      $a \le \lfloor sqrt(|D| / 4) \rfloor < sqrt(|D| / 4)$, the former explicitly, the latter by
      virtue of $D$ being odd (and therefore ensuring a fractional result for the ideal
      evaluation).

      We know our form is primitive as $a$ is prime and $b < a$.

      The `c` coefficient does satisfy the equation $b^2 - 4 a c = delta$.

      The discriminant was bound to be negative and odd, the former inherent by our treatment of
      it, the latter explicitly checked with an assertion.

      Therefore, this is safe to call.
    */
    let prime_ideal = unsafe {
      Self::from_coefficients(trim(a), (b_positive, trim(b_abs)), trim(c), trim(discriminant_abs))
    };
    prime_ideal.double()
  }
}
