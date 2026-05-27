use core::ops::Neg;
use std::sync::Arc;

use zeroize::Zeroize;

use crypto_bigint::{Choice, CtEq, CtSelect, Resize, BoxedUint};

use crate::Table;

mod numbers;
use numbers::*;

/// A constant-time element of a class group, implemented via crypto-bigint's `BoxedUint`.
///
/// This is implemented in time variable to the discriminant yet constant to `a, b`. This prevents
/// timing analysis from leaking the elements being composed. It will work with a discriminant of
/// any size yet is only recommended for provers as it has a significant performance overhead to
/// other backends, which verifiers should take advantage of.
#[derive(Clone, Debug)]
pub struct CryptoBigintHeapElement {
  a: UnsignedInteger,
  b: Integer,
  c: UnsignedInteger,
  discriminant: Arc<Integer>,
}

impl PartialEq for CryptoBigintHeapElement {
  fn eq(&self, other: &Self) -> bool {
    (self.a.ct_eq(&other.a) & self.b.ct_eq(&other.b) & self.discriminant.ct_eq(&other.discriminant))
      .into()
  }
}
impl Eq for CryptoBigintHeapElement {}

impl Zeroize for CryptoBigintHeapElement {
  fn zeroize(&mut self) {
    // Zeroize
    self.a.zeroize();
    self.b.zeroize();
    self.c.zeroize();

    // Set to the identity
    self.a = UnsignedInteger::from(BoxedUint::one_with_precision(self.max_bits_for_a()));
    self.b =
      Integer::from(UnsignedInteger::from(BoxedUint::one_with_precision(self.max_bits_for_b())));
    self.c = UnsignedInteger::from(
      BoxedUint::one().concatenating_add(&self.discriminant.abs().0).wrapping_shr(2),
    );
    self.c.0 = self.c.0.clone().resize(self.discriminant.abs().0.bits_precision());
  }
}

impl crypto_bigint::CtSelect for CryptoBigintHeapElement {
  fn ct_select(&self, b: &Self, choice: crypto_bigint::Choice) -> Self {
    Self {
      a: UnsignedInteger::ct_select(&self.a, &b.a, choice),
      b: Integer::ct_select(&self.b, &b.b, choice),
      c: UnsignedInteger::ct_select(&self.c, &b.c, choice),
      // Safe since `Element` is documented to have undefined behavior when mixed across class
      // groups
      discriminant: self.discriminant.clone(),
    }
  }
}

impl CryptoBigintHeapElement {
  fn max_bits_for_a(&self) -> u32 {
    // Lemma 5.3.4 of A Course in Computational Algebraic Number Theory
    self.discriminant.abs().0.bits_vartime().div_ceil(2)
  }

  fn max_bits_for_b(&self) -> u32 {
    // For reduced elements (as we have), `|b| <= a`
    self.max_bits_for_a()
  }

  fn reduce(
    log_2_a_bound: u32,
    a: UnsignedInteger,
    b: Integer,
    discriminant: Arc<Integer>,
  ) -> Self {
    // Reduce `b % 2a` to obtain a bound on the size of `b`
    // TODO: Remove this. We do it here to obtain a bound on the size of `b`, but we should have
    // better ways to determine this bound
    let b = &b % &(&a << 1);

    /*
      Resize `a, b` to their bounds

      We resize `a` to a slightly larger bound, as this is the bound used on both variables by the
      reduction algorithm. The reduction algorithm requires both variables have capacity capable of
      storing this bound.
    */
    let a = a.0.resize(1 + log_2_a_bound);
    let b = b.0.resize(1 + log_2_a_bound);

    let (a, b, c) = super::reduce(1 + log_2_a_bound, a, (Choice::TRUE, b), &discriminant.abs().0);
    let b_decomposed = b;

    // `b_decomposed` -> `b`, the integer
    let b = Integer::from(UnsignedInteger::from(b_decomposed.1));
    let b = <_>::ct_select(&-b.clone(), &b, b_decomposed.0);

    let mut res = Self { a: UnsignedInteger(a), b, c: UnsignedInteger(c), discriminant };

    // Resize `a, b, c`
    res.a.resize(res.max_bits_for_a());
    let max_bits_for_b = res.max_bits_for_b();
    res.b.abs_mut().resize(max_bits_for_b);
    res.c.resize(res.discriminant.abs().0.bits_precision());

    res
  }
}

impl crate::Element for CryptoBigintHeapElement {
  const MAX_TABLE_BITS: u32 = 8;

  fn is_identity(&self) -> subtle::Choice {
    // If `a == b`, as this is a reduced form, we know `b == |b|`, so we don't need to check `b`'s
    // sign
    (self.a.is_one() & self.b.abs().is_one()).into()
  }

  fn add(&self, other: &Self) -> CryptoBigintHeapElement {
    let mut a1 = self.a.clone();
    let mut b1 = self.b.clone();
    let mut a2 = other.a.clone();
    let mut b2 = other.b.clone();
    let c2 = other.c.clone();

    // `generic::add` requires `a1, a2` have a spare bit of capacity in their containers
    a1.resize(self.max_bits_for_a() + 1);
    a2.resize(self.max_bits_for_a() + 1);
    // and that the capacity of the `a` coefficients is equal the `b` coefficients' capacity
    b1.abs_mut().resize(self.max_bits_for_a() + 1);
    b2.abs_mut().resize(self.max_bits_for_a() + 1);

    let (a3, b3) = super::generic::add(
      a1.0,
      (b1.positive(), b1.into_abs().0),
      a2.0,
      (b2.positive(), b2.into_abs().0),
      c2.0,
    );

    let b3_abs = Integer::from(UnsignedInteger::from(b3.1));
    let b3 = <_>::ct_select(&-b3_abs.clone(), &b3_abs, b3.0);

    Self::reduce(
      2 * self.max_bits_for_a(),
      UnsignedInteger::from(a3),
      b3,
      self.discriminant.clone(),
    )
  }

  fn double(&self) -> CryptoBigintHeapElement {
    let mut a = self.a.clone();
    let mut b = self.b.clone();
    let c = self.c.clone();

    a.resize(self.max_bits_for_a() + 1);
    b.abs_mut().resize(self.max_bits_for_a() + 1);

    let (a3, b3) = super::generic::double(a.0, (b.positive(), b.into_abs().0), c.0);

    let b3_abs = Integer::from(UnsignedInteger::from(b3.1));
    let b3 = <_>::ct_select(&-b3_abs.clone(), &b3_abs, b3.0);

    Self::reduce(
      2 * self.max_bits_for_a(),
      UnsignedInteger::from(a3),
      b3,
      self.discriminant.clone(),
    )
  }

  fn sub(&self, other: CryptoBigintHeapElement) -> CryptoBigintHeapElement {
    self.add(&-other)
  }

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

  fn from_be_abc_discriminant_tess_root_unchecked(
    a: &[u8],
    b_positive: subtle::Choice,
    b: &[u8],
    c: &[u8],
    abs_value_of_neg_discriminant: &[u8],
    _tess_root: &[u8],
  ) -> Self {
    let b = Integer::from(UnsignedInteger::from_be_slice(b));
    // TODO: ct_neg
    let b = Integer::ct_select(&-b.clone(), &b, b_positive.into());

    let mut res = Self {
      a: UnsignedInteger::from_be_slice(a),
      b,
      c: UnsignedInteger::from_be_slice(c),
      discriminant: Arc::new(-Integer::from(UnsignedInteger::from_be_slice(
        abs_value_of_neg_discriminant,
      ))),
    };
    res.a.resize(res.max_bits_for_a());
    let max_bits_for_b = res.max_bits_for_b();
    res.b.abs_mut().resize(max_bits_for_b);
    res.c.resize(res.discriminant.abs().0.bits_vartime());
    res
  }

  fn a(&self) -> Vec<u8> {
    let mut bytes = self.a.to_be_bytes();
    while bytes.first() == Some(&0) {
      bytes.remove(0);
    }
    bytes
  }

  fn b(&self) -> (subtle::Choice, Vec<u8>) {
    let mut bytes = self.b.abs().to_be_bytes();
    while bytes.first() == Some(&0) {
      bytes.remove(0);
    }
    (self.b.positive().into(), bytes)
  }
}

impl Neg for CryptoBigintHeapElement {
  type Output = Self;
  fn neg(self) -> Self {
    Self::reduce(self.max_bits_for_a(), self.a, self.b.neg(), self.discriminant)
  }
}
