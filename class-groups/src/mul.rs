#[cfg(feature = "alloc")]
mod table {
  use core::num::NonZero;
  use alloc::{boxed::Box, vec::Vec};
  use crate::Element;

  /// A precomputed table for an element.
  ///
  /// no-`alloc`, this is constrained to the `bits = 1` case so that its memory may be statically
  /// defined. It exists to maintain the API, not to offer any performance benefit.
  pub struct Table<E> {
    pub(super) bits: u8,
    pub(super) element: Box<[E]>,
  }

  impl<E: Element> Table<E> {
    /// Create a new table of size up to $2^{bits}$.
    ///
    /// This MAY create a smaller table depending on certain limitations.
    pub fn new(bits: NonZero<u8>, element: E) -> Self {
      // We omit index `0`, corresponding to the identity, which makes indexing off by one
      let len = (1usize << u8::from(bits)) - 1;
      let mut table = Vec::with_capacity(len);
      table.push(element);
      for i in 2 ..= len {
        if (i % 2) == 0 {
          table.push(table[(i / 2) - 1].double());
        } else {
          table.push(table[i - 2].add(&table[0]));
        }
      }

      Self { bits: u8::from(bits), element: table.into() }
    }
  }
}

#[cfg(not(feature = "alloc"))]
mod table {
  use core::num::NonZero;
  use crate::Element;

  /// A precomputed table for an element.
  ///
  /// no-`alloc`, this is constrained to the `bits = 1` case so that its memory may be statically
  /// defined. It exists to maintain the API, not to offer any performance benefit.
  pub struct Table<E> {
    pub(super) bits: u8,
    pub(super) element: [E; 1],
  }

  impl<E: Element> Table<E> {
    /// Create a new table of size up to $2^{bits}$.
    ///
    /// This MAY create a smaller table depending on certain limitations.
    pub fn new(_bits: NonZero<u8>, element: E) -> Self {
      Self { bits: 1, element: [element] }
    }
  }
}

use crypto_bigint::{CtEq as _, CtAssign};
use crate::Element;
pub use table::*;

/// Extract a `table_bits`-sized chunk of bits from a little-endian encoded scalar.
///
/// This returns `Ok(chunk)` where chunk is the bits indexed from `bits .. (bits + table_bits)`
/// if `(bits < (8 * scalar.len())) && ((bits % table_bits) == 0)` (where `scalar` is considered
/// zero-extended if `bits < (8 * scalar.len()) < (bits + table_bits)`).
///
/// This returns `Err(distance)` if either:
/// - `(bits % table_bits) != 0`
/// - `bits >= (8 * table_bits)`
///
/// such that `bits - distance` is the next value for which this function will return `Ok`.
///
/// This DOES NOT require the bits be aligned to any byte boundaries.
#[expect(clippy::inline_always)]
#[inline(always)]
fn bit_chunk(scalar: &[u8], bits: usize, table_bits: u8) -> Result<usize, usize> {
  {
    let scalar_bits = 8 * scalar.len();
    if bits >= scalar_bits {
      let partial_bits = scalar_bits % usize::from(table_bits);
      let first_valid_bits = if partial_bits == 0 {
        scalar_bits - usize::from(table_bits)
      } else {
        scalar_bits - partial_bits
      };
      Err(bits - first_valid_bits)?;
    }
  }

  {
    let midway_through_bits = bits % usize::from(table_bits);
    if midway_through_bits != 0 {
      Err(midway_through_bits)?;
    }
  }

  // Find which bytes contain these bits
  let start_byte = bits / 8;
  let end_byte = (bits + usize::from(table_bits)).div_ceil(8);
  let mut bytes = scalar[start_byte .. end_byte.min(scalar.len())].iter();

  // Shift out the irrelevant bits from the first byte
  let shr = bits % 8;
  let mut result = usize::from(bytes.next().unwrap() >> shr);
  // Shift in the remaining bytes
  for (i, b) in bytes.enumerate() {
    result |= usize::from(*b) << ((8 * (1 + i)) - shr);
  }

  /*
    Mask off any bits which aren't relevant

    This is incorrect for the edge case `table_bits = usize::BITS`. However, Rust will have
    allocated a container to store elements of the table, and an allocation in Rust is limited to
    `isize::MAX`. Accordingly, it is impossible (not to mention absurd) to have a table with length
    `usize::BITS`.

    https://doc.rust-lang.org/1.85.0/core/primitive.pointer.html#method.offset
  */
  Ok(result & ((1 << table_bits) - 1))
}

impl<E: Element> Table<E> {
  /// A constant-time multi-scalar multiplication.
  ///
  /// `identity` MUST be the identity element. The scalars are specified via their little-endian
  /// encodings. All elements MUST have the same discriminant with this function having undefined
  /// behavior otherwise.
  ///
  /// This function is variable-time to the size of the discriminant, the length of the iterator,
  /// the size of the tables passed in, and the length of the scalars. It is independent to the
  /// tabled values, and the value of the scalars, so long as the underlying `E::double`, E::add`
  /// are.
  pub fn msm<'value>(
    identity: &E,
    iter: impl Copy + IntoIterator<Item = &'value (&'value [u8], &'value Table<E>)>,
  ) -> E
  where
    E: 'value + CtAssign,
  {
    let mut result = identity.clone();
    let mut bits = 8 * iter.into_iter().map(|(scalar, _table)| scalar.len()).max().unwrap_or(0);
    loop {
      let mut doubles = None;
      for (scalar, table) in iter {
        match bit_chunk(scalar, bits, table.bits) {
          Ok(index) => {
            // Select the element with a constant memory access pattern
            let mut to_add = identity.clone();
            for i in 1 ..= table.element.len() {
              to_add.ct_assign(&table.element[i - 1], i.ct_eq(&index));
            }
            result = result.add(&to_add);

            // The element should be doubled until this window is aligned again
            let doubles = doubles.get_or_insert(usize::from(table.bits));
            *doubles = (*doubles).min(usize::from(table.bits));
          }
          Err(distance) => {
            // The element should be doubled until this window is aligned
            let doubles = doubles.get_or_insert(distance);
            *doubles = (*doubles).min(distance);
          }
        }
      }

      // If we've handled the final chunk of bits, `break`
      if bits == 0 {
        break;
      }

      // Perform the necessary doublings to align with the next table
      let doubles = doubles.unwrap();
      for _ in 0 .. doubles {
        result = result.double();
      }
      bits -= doubles;
    }
    result
  }

  /// A variable-time multi-scalar multiplication.
  ///
  /// `identity` MUST be the identity element. The scalars are specified via their little-endian
  /// encodings. All elements MUST have the same discriminant with this function having undefined
  /// behavior otherwise.
  // Comments which would be duplicated with `Table::msm` are omitted.
  pub fn msm_vartime<'value>(
    identity: E,
    iter: impl Copy + IntoIterator<Item = &'value (&'value [u8], &'value Table<E>)>,
  ) -> E
  where
    E: 'value,
  {
    let mut result = identity;
    let mut bits = 8 * iter.into_iter().map(|(scalar, _table)| scalar.len()).max().unwrap_or(0);
    loop {
      let mut doubles = None;
      for (scalar, table) in iter {
        match bit_chunk(scalar, bits, table.bits) {
          Ok(index) => {
            if let Some(index) = index.checked_sub(1) {
              result = result.add(&table.element[index]);
            }
            let doubles = doubles.get_or_insert(usize::from(table.bits));
            *doubles = (*doubles).min(usize::from(table.bits));
          }
          Err(distance) => {
            let doubles = doubles.get_or_insert(distance);
            *doubles = (*doubles).min(distance);
          }
        }
      }

      if bits == 0 {
        break;
      }

      let doubles = doubles.unwrap();
      for _ in 0 .. doubles {
        result = result.double();
      }
      bits -= doubles;
    }
    result
  }
}
