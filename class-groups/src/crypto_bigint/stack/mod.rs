use core::ops::Neg;

use zeroize::Zeroize;

use crypto_bigint::{CtEq, CtSelect, Uint};

use crate::Table;

mod numbers;
use numbers::*;

// 2048-bit fundamental discriminant with 256-bit subgroup = 2560-bit discriminant
/*
  We use a further 128 bits for the misc additions/shifts we perform during steps. While ideally,
  we'd only use a further 64 bits, we need an even amount of limbs inside crypto-bigint.
*/
const BITS: u32 = 2688;

// We use `U` to represent `a` which is bounded by the square root of the absolute value of the
// discriminant, so its bit-length will be half of the absolute value of the discriminant's
const A_BITS: u32 = BITS / 2;
type U = Uint<{ crypto_bigint::nlimbs(A_BITS) }>;
// We use `I` to represent `b` which is bounded `-a < b < a`, so its absolute value fits into the
// same amount of bits as `a` does
type I = IStruct<Uint<{ crypto_bigint::nlimbs(A_BITS) }>>;

type WideU = Uint<{ crypto_bigint::nlimbs(BITS) }>;
type WideI = IStruct<WideU>;

/// A constant-time element of a class group, implemented via crypto-bigint's `Uint, Int`.
///
/// This is implemented in time variable to the discriminant yet constant to `a, b`. This prevents
/// timing analysis from leaking the elements being composed. It is only recommended for provers as
/// it has a significant performance overhead to other backends, which verifiers should take
/// advantage of.
///
/// The usage of `Uint, Int` means these elements live on the stack and are fixed size. They
/// accordingly only support discriminants of bounded size. Using a larger discriminant may cause a
/// runtime panic. The officially supported bound is a 2560-bit discriminant.
// TODO: Parameterize bits at a higher level
#[derive(Clone, Debug)]
pub struct CryptoBigintStackElement {
  a: U,
  b: I,
  c: WideU,
  discriminant_abs: WideU,
}

impl PartialEq for CryptoBigintStackElement {
  fn eq(&self, other: &Self) -> bool {
    let a = Self::reduce(self.a, self.b, self.discriminant_abs);
    let other = Self::reduce(other.a, other.b, other.discriminant_abs);
    (a.a.ct_eq(&other.a) & a.b.ct_eq(&other.b) & a.discriminant_abs.ct_eq(&other.discriminant_abs))
      .into()
  }
}
impl Eq for CryptoBigintStackElement {}

impl Zeroize for CryptoBigintStackElement {
  fn zeroize(&mut self) {
    // Zeroize
    self.a.zeroize();
    self.b.zeroize();
    self.c.zeroize();

    // Set to the identity
    self.a = U::ONE;
    self.b = I::from(U::ONE);
    self.c = (WideU::ONE + self.discriminant_abs).overflowing_shr_vartime(2).unwrap();
  }
}

impl crypto_bigint::CtSelect for CryptoBigintStackElement {
  fn ct_select(&self, b: &Self, choice: crypto_bigint::Choice) -> Self {
    Self {
      a: U::ct_select(&self.a, &b.a, choice),
      b: I::ct_select(&self.b, &b.b, choice),
      c: WideU::ct_select(&self.c, &b.c, choice),
      // Safe since `Element` is documented to have undefined behavior when mixed across class
      // groups
      discriminant_abs: self.discriminant_abs,
    }
  }
}

impl CryptoBigintStackElement {
  fn partial_reduce(a: WideU, b: WideI, discriminant_abs: WideU) -> Self {
    /*
      `partial_reduce` yields `a, b` coefficients which are bounded by the square root of delta, so
      the `a` from composition will be bounded by delta. The `b` coefficient is bound to be
      within one bit of twice the resulting `a` coefficient or within one bit of the `b2`
      coefficient used for composition, whichever is greater. As `b2` was also bounded by the
      square root of delta, we know the bound from `a` to be the greater (and therefore relevant)
      bound.
    */
    let (a, b_decomposed, c) = super::partial_reduce(
      2 + discriminant_abs.bits_vartime(),
      a,
      (b.positive, *b.abs()),
      &discriminant_abs,
    );
    let (a, a_hi) = a.split();
    debug_assert!(bool::from(a_hi.is_zero()));
    let (b_abs, b_abs_hi) = b_decomposed.1.split();
    debug_assert!(bool::from(b_abs_hi.is_zero()));
    let b = IStruct::from(b_abs).ct_neg(!b_decomposed.0);
    Self { a, b, c, discriminant_abs }
  }
  fn reduce(a: U, b: I, discriminant_abs: WideU) -> Self {
    let b_decomposed = (b.positive, *b.abs());
    let (a, b_decomposed, c) = super::reduce(
      discriminant_abs.bits_vartime().div_ceil(2),
      a.concat(&Uint::ZERO),
      (b_decomposed.0, b_decomposed.1.concat(&Uint::ZERO)),
      &discriminant_abs,
    );
    let a = a.split().0;
    let mut b = IStruct::from(b_decomposed.1.split().0);
    b.positive = b_decomposed.0;
    Self { a, b, c, discriminant_abs }
  }
}

impl crate::Element for CryptoBigintStackElement {
  const MAX_TABLE_BITS: u32 = 12;

  fn is_identity(&self) -> subtle::Choice {
    let a = Self::reduce(self.a, self.b, self.discriminant_abs);
    (a.a.ct_eq(&U::ONE) & a.b.ct_eq(&I::from(U::ONE))).into()
  }

  fn add(&self, other: &Self) -> CryptoBigintStackElement {
    let a1 = self.a;
    let b1 = self.b;
    let a2 = other.a;
    let b2 = other.b;
    let c2 = other.c;

    let (a3, b3) =
      super::generic::add(a1, (b1.positive, *b1.abs()), a2, (b2.positive, *b2.abs()), c2);

    Self::partial_reduce(a3, IStruct::from(b3.1).ct_neg(!b3.0), self.discriminant_abs)
  }

  fn double(&self) -> CryptoBigintStackElement {
    let a = self.a;
    let b = self.b;
    let c = self.c;

    let (a3, b3) = super::generic::double(a, (b.positive, *b.abs()), c);

    Self::partial_reduce(a3, IStruct::from(b3.1).ct_neg(!b3.0), self.discriminant_abs)
  }

  fn sub(&self, other: CryptoBigintStackElement) -> CryptoBigintStackElement {
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
    // We do not use `_tess_root` as we do not implement `PARTEUCL` (or similar)
    _tess_root: &[u8],
  ) -> Self {
    if (8 * abs_value_of_neg_discriminant.len()) > usize::try_from(BITS - 128).unwrap() {
      panic!("too large of a discriminant");
    }

    let full_bytes = |bits: usize, bytes: &[u8]| {
      let mut full_bytes = vec![0u8; bits / 8];
      full_bytes[(bits / 8) - bytes.len() ..].copy_from_slice(bytes);
      full_bytes
    };

    let b = I::from(U::from_be_slice(&full_bytes(usize::try_from(A_BITS).unwrap(), b)))
      .ct_neg(!crypto_bigint::Choice::from(b_positive));

    Self {
      a: U::from_be_slice(&full_bytes(usize::try_from(A_BITS).unwrap(), a)),
      b,
      c: WideU::from_be_slice(&full_bytes(usize::try_from(WideU::BITS).unwrap(), c)),
      discriminant_abs: WideU::from_be_slice(&full_bytes(
        usize::try_from(WideU::BITS).unwrap(),
        abs_value_of_neg_discriminant,
      )),
    }
  }

  fn a(&self) -> Vec<u8> {
    let bytes = Self::reduce(self.a, self.b, self.discriminant_abs).a.to_be_bytes();
    let mut start = 0;
    while bytes.get(start) == Some(&0) {
      start += 1;
    }
    bytes[start ..].to_vec()
  }

  fn b(&self) -> (subtle::Choice, Vec<u8>) {
    let b = Self::reduce(self.a, self.b, self.discriminant_abs).b;
    let bytes = b.abs().to_be_bytes();
    let mut start = 0;
    while bytes.get(start) == Some(&0) {
      start += 1;
    }
    (b.positive.into(), bytes[start ..].to_vec())
  }
}

impl Neg for CryptoBigintStackElement {
  type Output = Self;
  fn neg(mut self) -> Self {
    // We do not have to worry about if `b = 0` as `b` is odd when the discriminant is odd
    self.b.positive = !self.b.positive;
    self
  }
}
