use core::ops::Index;
use alloc::vec::Vec;

use crate::Element;

/// TODO
pub trait ElementExt: Element {
  /// The maximum amount of bits to create a table with.
  ///
  /// This allows backends which won't use larger tables to prevent redundant creation of such
  /// large tables;
  const MAX_TABLE_BITS: u32 = 16;

  /// Perform a multiexponentation.
  ///
  /// The implementation provided by this trait runs in variable time.
  #[must_use]
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
  #[must_use]
  fn mul(table: &Table<Self>, scalar: &[u8]) -> Self {
    Self::multiexp(&table[0], &[(table, scalar)])
  }
}

/// A table to perform multiplications with.
#[derive(Clone)]
pub struct Table<E: ElementExt>(usize, Vec<E>);
impl<E: ElementExt> Table<E> {
  /// Create a new table.
  ///
  /// This function executes in constant-time w.r.t. `element` if `double, add` are constant-time.
  #[must_use]
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
  #[must_use]
  pub fn new_for_scalar_bits(scalar_bits: usize, identity: E, element: E) -> Self {
    let mut bits = 0u32;
    let mut adds = usize::MAX;
    while {
      let new_bits = bits + 1;
      let new_adds =
        2usize.pow(new_bits) + (scalar_bits.min(8192) / usize::try_from(new_bits).unwrap());
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
  #[must_use]
  pub fn bits(&self) -> usize {
    self.0
  }
}

impl<E: ElementExt> AsRef<[E]> for Table<E> {
  fn as_ref(&self) -> &[E] {
    self.1.as_slice()
  }
}

impl<E: ElementExt> Index<usize> for Table<E> {
  type Output = E;
  fn index(&self, i: usize) -> &E {
    &self.1[i]
  }
}
