use core::ops::Neg;
use std::io;

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
/// forms with distinct discriminants are _always_ undefined behavior and MUST NOT be done.
///
/// Operations with the binary quadratic forms are not notated multiplicatively but additively.
/// The composition of two forms is referred to as addition, and the composition of a form with
/// itself is referred to as doubling. The inverse of an element is notated as its negation.
///
/// Implementations of this trait MAY run in variable time.
pub trait Element:
  Sized + Send + Sync + Clone + Neg<Output = Self> + PartialEq + Eq + core::fmt::Debug
{
  /// If this element is the identity.
  fn is_identity(&self) -> subtle::Choice;

  /// Double this element.
  ///
  /// This is generally faster than adding an element to itself as it's allowed to specialize on
  /// this special case.
  fn double(&self) -> Self;
  /// Add two elements.
  fn add(&self, other: &Self) -> Self;
  /// Subtract one element from another.
  fn sub(&self, other: Self) -> Self;

  /// Fetch the `a, b, c` coefficients of the single reduced form equivalent to this form and the
  /// absolute value of its discriminant.
  ///
  /// The coefficients and absolute value of the discriminant are little-endian encoded.
  /// `b` is represented by a sign bit, if `b` is positive (greater than or equal to zero), and the
  /// encoding of its absolute value. Values MAY have trailing zeroes.
  ///
  /// # Safety
  ///
  /// Implementations MUST return well-defined coefficients for a primitive _reduced_ positive
  /// definite binary quadratic form of a negative odd discriminant (the one whose value is
  /// yielded). It is undefined behavior to not do so, hence this being marked `unsafe`. It is only
  /// unsafe to _implement_. It MUST NOT be unsafe to _call_.
  #[expect(clippy::type_complexity)]
  unsafe fn a_b_c_discriminant(
    &self,
  ) -> (
    impl AsRef<[u8]>,
    (crypto_bigint::Choice, impl AsRef<[u8]>),
    impl AsRef<[u8]>,
    impl AsRef<[u8]>,
  );

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
  /// (un)compressed encodings which perform validation at time of decode.
  unsafe fn from_coefficients(
    a: impl AsRef<[u8]>,
    b: (crypto_bigint::Choice, impl AsRef<[u8]>),
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
  fn compress(&self, mut writer: impl io::Write) -> io::Result<()> {
    use crypto_bigint::{NonZero, BoxedUint};

    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, (b_positive, b_abs), _c, _discriminant) = unsafe { self.a_b_c_discriminant() };
    let a = a.as_ref();
    let b_abs = b_abs.as_ref();

    let a = BoxedUint::from_le_slice(a, u32::try_from(8 * a.len()).expect("4 GB `a` coefficient?"))
      .expect("container overflowed despite precision proportional to length of the encoding");
    let a = NonZero::new(a).expect("`a > 0` when `delta < 0`");

    let b_abs = BoxedUint::from_le_slice(
      b_abs,
      u32::try_from(8 * b_abs.len()).expect("4 GB `b` coefficient?"),
    )
    .expect("container overflowed despite precision proportional to length of the encoding");

    writer.write_all(&crate::crypto_bigint::encode_compressed_binary_quadratic_form(
      a, b_positive, b_abs,
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
          io::Error::other(format!(
            "container overflowed despite precision proportional to length of the encoding: {e:?}"
          ))
        })?,
      )
      .map_err(|e| io::Error::other(format!("{e:?}")))?;
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
  /// quadratic forms. Implementations MUST only error if the underlying IO errors, being
  /// error-free themselves.
  ///
  /// The provided implementation runs in variable time and MAY panic for absurdly large
  /// coefficients.
  #[cfg(feature = "std")]
  fn uncompressed_encode(&self, writer: impl io::Write) -> io::Result<()> {
    let _ = writer;
    todo!("TODO")
  }

  /// Decode an element of the specified discriminant without compression.
  ///
  /// This SHOULD NOT be used by protocols. The compressed encoding SHOULD be used unless there's
  /// an explicit reason to use uncompressed encodings (such as the stronger bounds on termination
  /// or amenability for constant-time implementations).
  ///
  /// This MUST implement the defined specification for the uncompressed decoding of binary
  /// quadratic forms. The discriminant MUST be negative and odd, specified by the little-endian
  /// encoding of its absolute value.
  ///
  /// The provided implementation runs in variable time and MAY panic for absurdly large
  /// discriminants.
  #[cfg(feature = "std")]
  fn uncompressed_decode(reader: impl io::Read, discriminant_abs: &[u8]) -> io::Result<()> {
    let _ = (reader, discriminant_abs);
    todo!("TODO")
  }

  /// Create an element of this type from another element.
  fn from(source: impl Element) -> Self {
    // SAFETY: `a_b_c_discriminant` is always safe to call
    let (a, b, c, discriminant) = unsafe { source.a_b_c_discriminant() };
    /*
      SAFETY: These coefficients must be well-defined for this to be safe,
      and `a_b_c_discriminant` is bounded to return well-defined coefficients.

      If we wanted a safe variant, we could instead defer to the uncompressed encoding, but that
      would validate the point on decode to ensure its safety (which is unnecessary for our
      purposes).
    */
    unsafe { Self::from_coefficients(a, b, c, discriminant) }
  }
}
