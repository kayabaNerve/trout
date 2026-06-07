use core::{ops::Neg, fmt::Debug};

use zeroize::Zeroize;

use crypto_bigint::{
  Choice, CtOption, CtEq, CtGt as _, CtSelect, CtAssign as _, BitOps, NonZero, One as _, Limb,
  UintRef,
};

use super::I;

use crate::{Element, Table};

pub(super) trait Limbs:
  Send
  + Sync
  + Debug
  + Zeroize
  + CtEq
  + CtSelect
  + BitOps
  + super::composition::Limbs<
    Wide: Send
            + Sync
            + Debug
            + Zeroize
            + CtSelect
            + BitOps
            + super::c::Limbs
            + super::reduction::Limbs,
  > + super::encoding::Limbs
{
  type Bytes: AsRef<[u8]> + AsMut<[u8]>;

  /// The maximum amount of bits this value can support.
  ///
  /// `None` signifies this value is unbounded.
  fn max_bits() -> Option<u32>;

  /// Truncate `wide` to a member of `Self`.
  ///
  /// `bits`, a bound on the size of the result, is provided. The value in `wide` MUST be less than
  /// $2^{bits}$. `bits` MUST be less than or equal to `Self::max_bits()` when
  /// `Self::max_bits().is_some()`.
  fn truncate(wide: Self::Wide, bits: u32) -> Self;

  /// Widen `thin` to a member of `Self::Wide`.
  ///
  /// `wide_bits` is a bound on how big the widened type should be able to support. The value in
  /// `thin` MUST be less than $2^{wide_bits}$. `wide_bits` MUST be less than or equal to
  /// `2 * Self::max_bits()` when `Self::max_bits().is_some()`.
  fn widen(thin: Self, wide_bits: u32) -> Self::Wide;

  /// Convert this number to a sequence of little-endian bytes.
  ///
  /// This function MUST run in constant time and yield a result of length constant to the relevant
  /// bound.
  fn to_le_bytes(self) -> Self::Bytes;

  /// Convert this wide number to a sequence of little-endian bytes.
  ///
  /// This function MUST run in constant time and yield a result of length constant to the relevant
  /// bound.
  fn wide_to_le_bytes(wide: Self::Wide) -> impl AsRef<[u8]>;

  /// Load this number from a sequence of little-endian bytes.
  ///
  /// The slice MAY be of arbitrary length so long as the encoded value has bits less than or
  /// equal to `max_bits`. `max_bits` MUST be less than or equal to `Self::max_bits()` when
  /// `Self::max_bits().is_some()`.
  fn from_le_slice(bytes: &[u8], max_bits: u32) -> Self;

  /// Load a wide number from a sequence of little-endian bytes.
  ///
  /// The slice MAY be of arbitrary length so long as the encoded value has bits less than or
  /// equal to `max_bits`.`max_bits` MUST be less than or equal to `2 * Self::max_bits()` when
  /// `Self::max_bits().is_some()`.
  fn wide_from_le_slice(bytes: &[u8], max_bits: u32) -> Self::Wide;

  /// Stich together two byte sequences into a single container of length `2 * bytes_per_element`.
  fn stitch(first: Self::Bytes, second: Self::Bytes, bytes_per_element: usize) -> impl AsRef<[u8]>;
}

/// A constant-time primitive element of a class group, implemented via `crypto-bigint`.
///
/// This only supports discriminants `delta` such that $delta < 0, |delta| \cong 1 \mod 2$.
///
/// This is implemented in time variable to the discriminant yet constant to the `a, b, c`
/// coefficients. This prevents timing analysis from leaking the elements being composed. It is
/// only recommended for provers as it has a significant performance overhead compared to other
/// backends, which verifiers should take advantage of.
///
/// This implementation does not itself allocate and can be used with [`crypto_bigint::Uint`] to
/// achieve elements which are fixed size and live on the stack, albeit only with support for a
/// bounded subset of discriminants. Alternatively, [`crypto_bigint::BoxedUint`] may be used to
/// support all discriminants, at the cost of using the heap.
#[expect(private_bounds)]
#[derive(Clone, Debug)]
pub struct CryptoBigintElement<U: Limbs> {
  /// The `a` coefficient.
  ///
  /// This may not be reduced but is bounded to less than the square root of the discriminant.
  a: U,

  /// The `b` coefficient.
  ///
  /// This may not be reduced but is bounded to have an absolute value less than the square root of
  /// the discriminant.
  b: I<U>,

  /// The `c` coefficient.
  ///
  /// This may not be reduced but is bounded to be less than the discriminant.
  /*
    This `c` coefficient satisfies `b^2 - 4ac = delta`. `b^2` is at most the discriminant itself.
    This means `4ac` can be at most `2 |delta|` (for a negative discriminant, as we bound). This
    means `ac` can be at most `2 |delta| / 4`, and therefore `c` itself is within that bound.
  */
  c: U::Wide,

  /// The absolute value of the negative discriminant for this form.
  ///
  /// This is used to recalculate the `c` coefficient after composition.
  discriminant_abs: U::Wide,
}

impl<U: Limbs> CtEq for CryptoBigintElement<U> {
  /// This MAY return an incorrect result for forms of different discriminants.
  fn ct_eq(&self, other: &Self) -> Choice {
    let a = self.clone().reduce();
    let other = other.clone().reduce();

    /*
      We do not check the `c` coefficient is equal, as if the `a, b` coefficients are equal, the
      `c` coefficient will be so long as these forms are of the same discriminant (and if not,
      we're allowed to return an incorrect result, which is why we don't check the discriminant).
    */
    a.a.ct_eq(&other.a) & a.b.0.ct_eq(&other.b.0) & a.b.1.ct_eq(&other.b.1)
  }
}

impl<U: Limbs> PartialEq for CryptoBigintElement<U> {
  fn eq(&self, other: &Self) -> bool {
    bool::from(self.ct_eq(other))
  }
}
impl<U: Limbs> Eq for CryptoBigintElement<U> {}

#[expect(private_bounds)]
impl<U: Limbs> CryptoBigintElement<U> {
  /// This is only valid for forms of negative odd discriminant.
  fn identity_from_discriminant(discriminant_abs: U::Wide) -> Self {
    /*
      The identity element has `a = 1`. As composition sets $a_3 = (a_1 * a_2) / gcd(a_1, a_2)^2$,
      it's clear how having one $a_1 = 1$ causes $a_3 = a_2$ (or $a_2 = 1$ causes $a_3 = a_1$). As
      for the `b` coefficient, the only `b` coefficient less than or equal to an `a` coefficient of
      `1` (as required for a reduced form) is itself `1`. As `|b| == a`, then `b` must be positive.
      Finally, for the `c` coefficient, we are able to calculate it from the `a, b` coefficients
      and the discriminant.

      The identity element is primitive as `gcd(a, b, c) = gcd(1, 1, c) = 1`.
    */
    let a = &[1];
    let b = (Choice::TRUE, &[1]);

    /*
      `b^2 - 4ac = delta`
      `b^2 - delta = 4ac`
      `(b^2 - delta) / 4a = c`

      where `b^2 = 1, delta < 0, a = 1` so

      $(1 + |delta|) / 4 = c$
    */
    let mut c = discriminant_abs.clone();
    {
      let c = AsMut::<[Limb]>::as_mut(&mut c);
      let mut i = 0;
      let mut carry = Limb::ONE;
      while i < c.len() {
        // `|delta| >> 2`
        if let Some(j) = i.checked_sub(1) {
          c[j] |= c[i] << (Limb::BITS - 2);
        }
        c[i] >>= 2;
        /*
          `+ 1`, as `carry` was initialized to one.

          This technically doesn't calculate $(1 + |delta|) / 4$ but $floor(|delta| / 4) + 1$.
          These two values are equivalent when $|delta| \cong 3 \mod 4$.

          We only explicitly bound $delta < 0, delta \cong 1 \mod 2$. By $b^2 - 4 a c = delta$, we
          have $b^2 \cong delta \mod 4$. $3$ is not a square modulo $4$, so if
          $delta \cong 1 \mod 2$ (as we bound), we MUST have $delta \cong 1 \mod 4$ (and therefore
          $|delta| \cong 3 \mod 4$).
        */
        (c[i], carry) = c[i].carrying_add(Limb::ZERO, carry);
        i += 1;
      }
    }

    // SAFETY: This is well-defined, reduced, and primitive
    unsafe {
      <Self as Element>::from_coefficients(
        a,
        b,
        U::wide_to_le_bytes(c),
        U::wide_to_le_bytes(discriminant_abs),
      )
    }
  }
}

impl<U: Limbs> Zeroize for CryptoBigintElement<U> {
  /// This is only valid for forms of negative odd discriminant.
  ///
  /// This does not zeroize the discriminant, solely the `a, b, c` coefficients, and will set the
  /// result to the identity element of the same discriminant.
  fn zeroize(&mut self) {
    // Zeroize
    self.a.zeroize();
    // Best effort, as `Choice: !Zeroize`
    self.b.0.ct_assign(&Choice::TRUE, Choice::TRUE);
    self.b.1.zeroize();
    self.c.zeroize();

    *self = Self::identity_from_discriminant(self.discriminant_abs.clone());
  }
}

impl<U: Limbs> CtSelect for CryptoBigintElement<U> {
  /// This MAY return an incorrect result for forms of different discriminants.
  fn ct_select(&self, b: &Self, choice: Choice) -> Self {
    Self {
      a: U::ct_select(&self.a, &b.a, choice),
      b: (<_>::ct_select(&self.b.0, &b.b.0, choice), <_>::ct_select(&self.b.1, &b.b.1, choice)),
      c: U::Wide::ct_select(&self.c, &b.c, choice),
      // This is the same when the forms are of the same discriminant, allowing us to simply use
      // `self`'s without invoking `ct_select`
      discriminant_abs: self.discriminant_abs.clone(),
    }
  }
}

impl<U: Limbs> Neg for CryptoBigintElement<U> {
  type Output = Self;
  /// This is only correct for primitives forms where $delta \cong 1 \mod 2$.
  fn neg(mut self) -> Self {
    /*
      Per Proposition 5.2.5 of A Course in Computational Algebraic Number Theory, a binary
      quadratic form is only invertible if `(a, b, c)` is primitive, hence why we bound the input
      to be primitive.

      Proposition 5.2.5 also includes a very academic description of the inverse, which here is
      implemented as negating the `b` coefficient.

      While `-0` is of unclear validity in this context, we know that this result will _NOT_ be
      `-0` as $b \cong 1 \mod 2$ for odd discriminants (as we bound).
    */
    self.b.0 = !self.b.0;
    self
  }
}

#[expect(private_bounds)]
impl<U: Limbs> CryptoBigintElement<U> {
  /// Partially reduce an element.
  ///
  /// This assumes the coefficients are the result from composition (either addition or doubling)
  /// of two well-defined instances of this type.
  fn partial_reduce(a: U::Wide, b: I<U::Wide>, discriminant_abs: U::Wide) -> Self {
    /*
      `partial_reduce` yields `a, b` coefficients which are bounded by the square root of delta, so
      the `a` from composition will be bounded by delta. The `b` coefficient is bound to be
      within one bit of twice the resulting `a` coefficient or within one bit of the `b2`
      coefficient used for composition, whichever is greater. As `b2` was also bounded by the
      square root of delta, we know the bound from `a` to be the greater (and therefore the
      relevant) bound.
    */
    let (a, b, c) =
      super::partial_reduce(2 + discriminant_abs.bits_vartime(), a, b, &discriminant_abs);

    /*
      `partial_reduce` is guaranteed to return `a, b` which are each less then the square root of
      the discriminant. We need one additional bit for these to be usable with our methods for
      composition however.
    */
    let sqrt_discriminant_bits = discriminant_abs.bits_vartime().div_ceil(2);
    let a = U::truncate(a, 1 + sqrt_discriminant_bits);
    let b = (b.0, U::truncate(b.1, 1 + sqrt_discriminant_bits));
    // These `a, b` coefficients are bounded by the square root of delta, as this type requires
    // `c`'s bound, that it's bounded by the discriminant, is inherently satisfied from there
    Self { a, b, c, discriminant_abs }
  }

  /// Reduce an element.
  fn reduce(self) -> Self {
    let discriminant_bits = self.discriminant_abs.bits_vartime();
    let sqrt_discriminant_bits = discriminant_bits.div_ceil(2);
    let (a, b, c) = super::reduce(
      // The documentation on our `struct` require `a, b` satisfy this bound
      sqrt_discriminant_bits,
      // Widen these, as `reduce` requires all its arguments have the same capacity
      U::widen(self.a, discriminant_bits),
      (self.b.0, U::widen(self.b.1, discriminant_bits)),
      self.c,
    );

    /*
      A reduced element has `|b| <= a < sqrt(|delta|)` per
      Definition 5.3.2 and Lemma 5.3.4 of A Course in Computational Algebraic Number Theory.

      We again keep one extra bit for these to be usable with our methods for composition.
    */
    let a = U::truncate(a, 1 + sqrt_discriminant_bits);
    let b = (b.0, U::truncate(b.1, 1 + sqrt_discriminant_bits));
    Self { a, b, c, discriminant_abs: self.discriminant_abs.clone() }
  }
}

// SAFETY: This reduces the form before yielding it and does return a well-defined form as
// required.
unsafe impl<U: Limbs> crate::Coefficients for CryptoBigintElement<U> {
  /// This function runs in constant time.
  fn a_b_c_discriminant(
    self,
  ) -> (impl AsRef<[u8]>, (Choice, impl AsRef<[u8]>), impl AsRef<[u8]>, impl AsRef<[u8]>) {
    let reduced = self.reduce();
    (
      reduced.a.to_le_bytes(),
      (reduced.b.0, reduced.b.1.to_le_bytes()),
      U::wide_to_le_bytes(reduced.c),
      U::wide_to_le_bytes(reduced.discriminant_abs),
    )
  }
}

impl<U: Limbs> Element for CryptoBigintElement<U> {
  /// This is only valid for forms of negative odd discriminant.
  fn identity(discriminant_abs: impl AsRef<[u8]>) -> Self {
    let discriminant_abs = discriminant_abs.as_ref();
    assert_eq!(discriminant_abs[0] & 0b11, 0b11, "discriminant was not a valid odd discriminant");
    Self::identity_from_discriminant(U::wide_from_le_slice(
      discriminant_abs,
      8 * u32::try_from(discriminant_abs.len()).expect("4 GB discriminant?"),
    ))
  }

  /// This MAY return an incorrect result when the form doesn't have an odd, negative discriminant.
  fn is_identity(&self) -> Choice {
    let reduced = self.clone().reduce();

    let a = AsRef::<[Limb]>::as_ref(&reduced.a);
    let b = AsRef::<[Limb]>::as_ref(&reduced.b.1);

    /*
      We know the `a, b` coefficients are non-zero due to having a negative odd discriminant. We
      check both have only the least-significant bit set.
    */
    let is_one = a[0] | b[0];
    let mut is_zero = Limb::ZERO;
    for limb in &a[1 ..] {
      is_zero |= *limb;
    }
    for limb in &b[1 ..] {
      is_zero |= *limb;
    }
    is_one.is_one() & is_zero.is_zero()
  }

  /// This is only correct for forms of the same discriminant where at least one form is primitive.
  fn add(&self, other: &Self) -> Self {
    let (a3, b3) =
      super::add(self.a.clone(), self.b.clone(), other.a.clone(), other.b.clone(), other.c.clone());
    Self::partial_reduce(a3, b3, self.discriminant_abs.clone())
  }

  /// This is only correct when the form is primitive.
  fn double(&self) -> Self {
    let (a3, b3) = super::double(self.a.clone(), self.b.clone(), self.c.clone());
    Self::partial_reduce(a3, b3, self.discriminant_abs.clone())
  }

  /// This is only correct for forms of the same discriminant where at least one form is primitive.
  fn sub(&self, other: Self) -> Self {
    let (a3, b3) = super::add(
      self.a.clone(),
      self.b.clone(),
      other.a.clone(),
      (!other.b.0, other.b.1.clone()),
      other.c.clone(),
    );
    Self::partial_reduce(a3, b3, self.discriminant_abs.clone())
  }

  /// This function is only valid for primitive reduced positive definite binary quadratic forms of
  /// negative odd discriminant where the discriminant fits within `(2 * max_bits) - 2` bits.
  ///
  /// This function MAY run in time variable to:
  /// - the byte-length of the inputs
  /// - the validity of the inputs
  /// - the discriminant
  ///
  /// This function MAY panic if asked to handle coefficients which exceed the capacity of the
  /// underlying container(s).
  unsafe fn from_coefficients(
    a: impl AsRef<[u8]>,
    (b_positive, b_abs): (Choice, impl AsRef<[u8]>),
    c: impl AsRef<[u8]>,
    discriminant_abs: impl AsRef<[u8]>,
  ) -> Self {
    let a = a.as_ref();
    let b_abs = b_abs.as_ref();
    let c = c.as_ref();
    let discriminant_abs = discriminant_abs.as_ref();

    let bit_len = |slice: &[u8]| {
      if let Some(last) = slice.last() {
        u32::try_from(8 * (slice.len() - 1))
          .ok()
          .and_then(|value| value.checked_add(Limb::from(*last).bits()))
          .expect("slice exceeded 4 GB")
      } else {
        0
      }
    };

    // Determine how many bits are actually in the absolute value of the discriminant
    let discriminant_bits =
      U::wide_from_le_slice(discriminant_abs, bit_len(discriminant_abs)).bits_vartime();
    // Ensure our bound on the discriminant is respected
    if let Some(max_bits) = U::max_bits() {
      assert!(discriminant_bits <= ((2 * max_bits) - 2));
    }

    // Load the absolute value of the discriminant with the exact precision required
    let discriminant_abs = U::wide_from_le_slice(discriminant_abs, discriminant_bits);

    let sqrt_discriminant_bits = discriminant_bits.div_ceil(2);
    let a = U::from_le_slice(a, 1 + sqrt_discriminant_bits);
    assert!(bool::from(!a.bits().ct_gt(&sqrt_discriminant_bits)));
    let b = (b_positive, U::from_le_slice(b_abs, 1 + sqrt_discriminant_bits));
    assert!(bool::from(!b.1.bits().ct_gt(&sqrt_discriminant_bits)));
    let c = U::wide_from_le_slice(c, discriminant_bits);

    Self { a, b, c, discriminant_abs }
  }

  /// This runs in time variable to the size of the discriminant and the size of the underlying
  /// container.
  fn uncompressed_encode(&self) -> impl AsRef<[u8]> {
    let bits_per_element = (self.discriminant_abs.bits() / 2) + 1;
    let bytes_per_element = usize::try_from(bits_per_element.div_ceil(8)).unwrap();

    let reduced = self.clone().reduce();
    let a = reduced.a.to_le_bytes();
    let mut b = reduced.b.1.to_le_bytes();
    b.as_mut()[0] ^= u8::from(!reduced.b.0);

    U::stitch(a, b, bytes_per_element)
  }

  /// This runs in time variable to the size of the discriminant and the size of the underlying
  /// container. This MAY return `None` for discriminants which fit within the bounds but have
  /// trailing zero bytes which cause the amount of encoded bits to exceed the bounds.
  fn uncompressed_decode(
    buf: impl AsRef<[u8]>,
    discriminant_abs: impl AsRef<[u8]>,
  ) -> CtOption<Self> {
    let discriminant_abs = discriminant_abs.as_ref();

    let invalid_size = CtOption::new(
      Self {
        a: U::from_le_slice(&[], 1),
        b: (Choice::TRUE, U::from_le_slice(&[], 1)),
        c: U::wide_from_le_slice(&[], 1),
        discriminant_abs: U::wide_from_le_slice(&[], 1),
      },
      Choice::FALSE,
    );
    let discriminant_bits = {
      let Ok(discriminant_bytes) = u32::try_from(discriminant_abs.len()) else {
        return invalid_size;
      };
      let Some(msb) = discriminant_abs.last().copied() else { return invalid_size };
      /*
        This is lossy in that it _may_ believe a discriminant is larger than it actually is, but
        only if the discriminant has trailing zero bytes, which we're allowed to not support.
      */
      let Some(discriminant_bits) = 8u32.checked_mul(discriminant_bytes) else {
        return invalid_size;
      };
      let discriminant_bits = discriminant_bits - (8 - Limb::from(msb).bits());

      if let Some(max_bits) = U::max_bits() &&
        (discriminant_bits > (2u32.checked_mul(max_bits).unwrap_or(0).saturating_sub(2)))
      {
        return invalid_size;
      }

      discriminant_bits
    };

    let discriminant_bits =
      UintRef::new(U::wide_from_le_slice(discriminant_abs, discriminant_bits).as_ref()).bits();
    let discriminant_abs = U::wide_from_le_slice(discriminant_abs, discriminant_bits);

    let bits_per_element = (discriminant_abs.bits() / 2) + 1;
    let bytes_per_element = usize::try_from(bits_per_element.div_ceil(8)).unwrap();

    let buf = buf.as_ref();
    if buf.len() != (2 * bytes_per_element) {
      return invalid_size;
    }

    let sqrt_discriminant_bits = discriminant_bits.div_ceil(2);
    let a = U::from_le_slice(&buf[.. bytes_per_element], 1 + sqrt_discriminant_bits);
    let mut b_abs = U::from_le_slice(&buf[bytes_per_element ..], 1 + sqrt_discriminant_bits);

    let b_positive =
      (b_abs.as_ref()[0] & Limb::ONE).ct_eq(&(discriminant_abs.as_ref()[0] & Limb::ONE));
    b_abs.as_mut()[0] ^= Limb::from(u8::from(!b_positive));

    NonZero::new(a).and_then(|a| {
      super::encoding::validate_binary_quadratic_form(a, (b_positive, b_abs), &discriminant_abs)
        .map(|(a, b, c)| Self { a: a.get(), b, c, discriminant_abs })
    })
  }
}

// TODO
#[cfg(feature = "alloc")]
impl<U: Limbs> crate::ElementExt for CryptoBigintElement<U> {
  const MAX_TABLE_BITS: u32 = 12;

  /// This is only correct when `identity` is in fact the identity element for the class group the
  /// elements in the table belong to.
  fn multiexp(identity: &Self, pairs: &[(&Table<Self>, &[u8])]) -> Self {
    let mut longest_scalar_bits = 0;
    for (_table, scalar) in pairs {
      longest_scalar_bits = longest_scalar_bits.max(scalar.len() * 8);
    }

    let mut res: Option<Self> = None;
    for i in 0 .. longest_scalar_bits {
      // Shift over the existing result by a bit
      if let Some(res) = res.as_mut() {
        *res = res.double();
      }

      for (table, scalar) in pairs {
        let scalar_bits = scalar.len() * 8;
        // Transform the index of the bit in our longest scalar to the index of the bit in this one
        let Some(i) = i.checked_sub(longest_scalar_bits - scalar_bits) else {
          // If we're indexing a bit which doesn't exist in this scalar, continue
          continue;
        };

        // If it's time to add this entry, do so
        let table_bits = table.bits();
        if ((i + 1) % table_bits) == 0 {
          let mut accum = 0usize;
          debug_assert_eq!(i - (i + 1 - table_bits) + 1, table_bits);
          for i in (i + 1 - table_bits) ..= i {
            accum <<= 1;
            accum |= (usize::from(scalar[i / 8] >> (7 - (i % 8)))) & 1;
          }

          let mut to_add = Self::ct_select(&table[0], &table[1], 1.ct_eq(&accum));
          for i in 2 .. table.as_ref().len() {
            to_add = Self::ct_select(&to_add, &table[i], i.ct_eq(&accum));
          }
          res = Some(res.as_ref().map(|res| res.add(&to_add)).unwrap_or_else(|| to_add.clone()));
        }
      }
    }

    // Perform the final step of the accumulator
    for (table, scalar) in pairs {
      let scalar_bits = scalar.len() * 8;

      let table_bits = table.bits();
      let mut accum = 0usize;
      for i in ((scalar_bits / table_bits) * table_bits) .. scalar_bits {
        accum <<= 1;
        accum |= (usize::from(scalar[i / 8] >> (7 - (i % 8)))) & 1;
      }

      let mut to_add = Self::ct_select(&table[0], &table[1], 1.ct_eq(&accum));
      for i in 2 .. table.as_ref().len() {
        to_add = Self::ct_select(&to_add, &table[i], i.ct_eq(&accum));
      }
      res = Some(res.as_ref().map(|res| res.add(&to_add)).unwrap_or_else(|| to_add.clone()));
    }

    res.unwrap_or_else(|| identity.clone())
  }
}
