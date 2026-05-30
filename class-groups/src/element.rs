use core::ops::{Index, Neg};
use std::io;

/// An element of a class group.
///
/// This is a member of a specific class group. The operations on it are not expected to enforce
/// it's only used with members of the same class group. Mixing class groups causes undefined
/// behavior.
///
/// Implementations are allowed to define if they execute in variable or constant time, even for
/// methods working with types expected to be used in a constant-time context.
pub trait Element:
  Sized + Send + Sync + Clone + Neg<Output = Self> + PartialEq + Eq + core::fmt::Debug
{
  /// The maximum amount of bits to create a table with.
  ///
  /// This allows backends which won't use larger tables to prevent redundant creation of such
  /// large tables;
  const MAX_TABLE_BITS: u32 = 16;

  /// Returns if the element is identity.
  fn is_identity(&self) -> subtle::Choice;

  /// Double the element.
  fn double(&self) -> Self;
  /// Add two elements.
  fn add(&self, other: &Self) -> Self;
  /// Subtract one element from another.
  fn sub(&self, other: Self) -> Self;

  /// Perform a multiexponentation.
  ///
  /// The implementation provided by this trait runs in variable time.
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

          if accum != 0 {
            let to_add = &table[accum];
            res = Some(res.as_ref().map(|res| res.add(to_add)).unwrap_or_else(|| to_add.clone()));
          }
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

      if accum != 0 {
        let to_add = &table[accum];
        res = Some(res.as_ref().map(|res| res.add(to_add)).unwrap_or_else(|| to_add.clone()));
      }
    }

    res.unwrap_or_else(|| identity.clone())
  }

  /// Perform a multiplication with a `Table`.
  ///
  /// The scalar is expected to be represented by its big-endian bytes.
  ///
  /// The implementation provided by this trait is as-constant-time as `multiexp` is.
  fn mul(table: &Table<Self>, scalar: &[u8]) -> Self {
    Self::multiexp(&table[0], &[(table, scalar)])
  }

  /// Perform a multiplication.
  ///
  /// `mul` should be preferred where possible. This method is named the way it is as it only makes
  /// sense for use with elements which will not be scaled multiple times.
  ///
  /// The scalar is expected to be represented by its big-endian bytes.
  ///
  /// The implementation provided by this trait is as-constant-time as `double, add, mul` are.
  fn mul_once(identity: Self, element: Self, scalar: &[u8]) -> Self {
    Self::mul(&Table::new_for_scalar_bits(scalar.len() * 8, identity, element), scalar)
  }

  /// Parse an element from the big-endian encoding of its coordinates, the absolute value of the
  /// negative discriminant, and the floored tesseract (fourth) root of the absolute value of the
  /// discriminant divided by four.
  ///
  /// This does not check for consistency between the discriminant of the coordinates and the
  /// provided root, nor that the coordinates were reduced. It MUST only be called with validated
  /// arguments.
  fn from_be_abc_discriminant_tess_root_unchecked(
    a: &[u8],
    b_positive: subtle::Choice,
    b: &[u8],
    c: &[u8],
    abs_value_of_neg_discriminant: &[u8],
    tess_root: &[u8],
  ) -> Self;

  /// Fetch the `a`-coordinate of an element, big-endian encoded.
  fn a(&self) -> Vec<u8>;

  /// Fetch the `b`-coordinate of an element, big-endian encoded.
  ///
  /// The `Choice` represents the sign and is to be `0` if `b` is negative and `1` otherwise.
  fn b(&self) -> (subtle::Choice, Vec<u8>);

  /// Compress an element.
  #[cfg(feature = "std")]
  fn compress(&self, mut writer: impl io::Write) -> io::Result<()> {
    use crypto_bigint::{NonZero, BoxedUint};

    let a = self.a();
    let a =
      BoxedUint::from_be_slice(&a, u32::try_from(8 * a.len()).expect("4 GB `a` coefficient?"))
        .expect("container overflowed despite precision proportional to length of the encoding");
    let a = NonZero::new(a).expect("`a > 0` when `delta < 0`");

    let (b_positive, b_abs) = self.b();
    let b_abs = BoxedUint::from_be_slice(
      &b_abs,
      u32::try_from(8 * b_abs.len()).expect("4 GB `b` coefficient?"),
    )
    .expect("container overflowed despite precision proportional to length of the encoding");

    writer.write_all(&crate::crypto_bigint::encode_compressed_binary_quadratic_form(
      a,
      crypto_bigint::Choice::from(b_positive),
      b_abs,
    ))
  }
}

/// A table to perform multiplications with.
#[derive(Clone)]
pub struct Table<E: Element>(usize, Vec<E>);
impl<E: Element> Table<E> {
  /// Create a new table.
  ///
  /// This function executes in constant-time w.r.t. `element` if `double, add` are constant-time.
  pub fn new(bits: u32, identity: E, element: E) -> Self {
    let bits = bits.clamp(1, E::MAX_TABLE_BITS);
    let len = 2usize.pow(bits);
    let mut res = Vec::with_capacity(len);
    res.push(identity);
    res.push(element);

    for i in 2 .. len {
      // Check if we can calculate this with solely a doubling
      if (i % 2) == 0 {
        res.push(res[i / 2].double());
      } else {
        let next = res[i - 1].add(&res[1]);
        res.push(next);
      }
    }
    Self(usize::try_from(bits).unwrap(), res)
  }

  /// Create a new table of size optimal for a scalar-length.
  ///
  /// This is usable in ad-hoc multiplications where creating the table, and performing the
  /// multiplication with it, should not cost more than performing the multiplication out-right.
  pub fn new_for_scalar_bits(scalar_bits: usize, identity: E, element: E) -> Self {
    let mut bits = 0u32;
    let mut adds = usize::MAX;
    while {
      let new_bits = bits + 1;
      let new_adds = 2usize.pow(new_bits) + (scalar_bits.min(8192) / (new_bits as usize));
      if new_adds <= adds {
        bits = new_bits;
        adds = new_adds;
        true
      } else {
        false
      }
    } {}
    Self::new(bits, identity, element)
  }

  /// The bits preprocessed by this table.
  pub fn bits(&self) -> usize {
    self.0
  }
}

impl<E: Element> AsRef<[E]> for Table<E> {
  fn as_ref(&self) -> &[E] {
    self.1.as_slice()
  }
}

impl<E: Element> Index<usize> for Table<E> {
  type Output = E;
  fn index(&self, i: usize) -> &E {
    &self.1[i]
  }
}
