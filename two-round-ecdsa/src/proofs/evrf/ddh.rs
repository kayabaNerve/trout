use core::{marker::PhantomData, ops::Deref};
use std::io::{self, Read, Write};

use subtle::ConditionallySelectable;
use zeroize::{Zeroize, Zeroizing};
use rand::CryptoRng;

use group::{
  Group, GroupEncoding,
  prime::PrimeGroup,
  ff::{Field, PrimeField, PrimeFieldBits},
};
use ciphersuite::{group::ff::FromUniformBytes, Ciphersuite};

use generalized_bulletproofs::*;
use generalized_bulletproofs_circuit_abstraction::*;

use crate::{DigestReader, DigestWriter, Evrf, Parameters};

/// A curve which is embedded into another curve.
pub trait EmbeddedCurve:
  Zeroize + ConditionallySelectable + PrimeGroup<Scalar: Zeroize + PrimeFieldBits>
{
  /// The field this elliptic curve is defined over.
  type FieldElement: PrimeField;
  /// The `a` constant from the equation `y**2 = x**3 + ax + b`.
  fn a() -> Self::FieldElement;
  /// The `b` constant from the equation `y**2 = x**3 + ax + b`.
  fn b() -> Self::FieldElement;
  /// Convert the point to its `x`, `y` coordinates, returning `None` if identity.
  ///
  /// This function MUST execute in constant-time for points which aren't identity.
  fn to_xy(&self) -> Option<(Self::FieldElement, Self::FieldElement)>;
}

#[cfg(feature = "secp256k1")]
impl EmbeddedCurve for secq256k1::Point {
  type FieldElement = k256::Scalar;
  fn a() -> Self::FieldElement {
    <secq256k1::Point as ec_divisors::DivisorCurve>::a()
  }
  fn b() -> Self::FieldElement {
    <secq256k1::Point as ec_divisors::DivisorCurve>::b()
  }
  fn to_xy(&self) -> Option<(Self::FieldElement, Self::FieldElement)> {
    <secq256k1::Point as ec_divisors::DivisorCurve>::to_xy(*self)
  }
}

// Equation 9, yet scaling G_s as we have no futher use for the discrete logarithms over G_s
// We also don't populate for `0 ..= l` yet `0 .. windows`
fn C<G: EmbeddedCurve>() -> Vec<G> {
  let windows = (G::Scalar::NUM_BITS / 3) + u32::from(u8::from((G::Scalar::NUM_BITS % 3) != 0));
  let mut carry = 0;
  let res = (0 .. windows)
    .map(|i| {
      G::generator() *
        (if i != (windows - 1) {
          let i = u64::from(i) + 2;
          carry += i;
          G::Scalar::from(i)
        } else {
          -G::Scalar::from(carry)
        })
    })
    .collect::<Vec<_>>();

  // We use debug assertions to assert the validity of this as it's only invalid for trivial moduli
  debug_assert!({
    // Sum of all prior elements
    let mut carry = G::identity();
    let mut valid = true;
    for i in 1 .. (res.len() - 1) {
      carry += res[i - 1];
      // is not in the set {0, res[i], -res[i]}
      if bool::from(carry.is_identity()) || (carry == res[i]) || (carry == -res[i]) {
        valid = false;
        break;
      }
    }
    valid
  });
  debug_assert!(bool::from(res.iter().sum::<G>().is_identity()));

  res
}

// This is the preprocess of `C[i].to_xy()`
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone)]
struct CXY<F: PrimeField>(Vec<(F, F)>);
impl<F: PrimeField> CXY<F> {
  fn new<G: EmbeddedCurve<FieldElement = F>>(C: &[G]) -> Self {
    Self(C.iter().map(|point| point.to_xy().unwrap()).collect())
  }
}

// Claim 1, which we embed into the setup to avoid the cost per-invocation
/*
  The eVRF paper describes commiting to $k$ (sampled from $[0, s - 1]$) over $G_{T,1}$.
  $G_{T,1}$ is of order $q$, enabling an adversary to sample from $[0, s - 1 - q]$ and open as
  $k$ or $k + q$, or to sample from $[q, s - 1]$ and open as $k$ or $k - q$. This assumes
  $q < s$. We can add the bound $q < s$, yet for the popular secp256k1 curve, it inherently
  forms a cycle with secq256k1. The order of secq256k1 is greater than the order of secp256k1
  and would be disqualified by this bound, forcing finding (and justifying) an alternative
  curve.

  Distinctly, the eVRF paper describes a single Pedersen Commitment over multiple generators
  ($G_{T,n}$). This would be a Pedersen Vector Commitment which Bulletproofs, as published, does
  _not_ support. It's Generalized Bulletproofs which extends Bulletproofs' R1CS statement regarding
  vector commitments.

  Due to the problems with the described scheme, and to avoid the cost of the bits per invocation,
  we instead define the commitment to $k$ to be a vector commitment to its bits. We then modify
  $\pi_Q$ to prove it's well-formed accordingly. This does not extend the definition of
  Bulletproofs present in the eVRF paper (as it defines Generalized Bulletproofs) and enables
  reducing the IPA rows (for a 256-bit curve) to the next power of two.
*/
struct DiscreteLogarithm<G: EmbeddedCurve>(PhantomData<G>);
impl<G: EmbeddedCurve> DiscreteLogarithm<G> {
  fn bit(i: usize) -> Variable {
    debug_assert!(i < usize::try_from(G::Scalar::NUM_BITS).unwrap());
    Variable::CG { commitment: 0, index: i }
  }
  fn three_bit_table_products(i: usize) -> (Variable, Variable, Variable, Variable) {
    debug_assert!(i < usize::try_from(G::Scalar::NUM_BITS / 3).unwrap());
    (
      Variable::CG {
        commitment: 0,
        index: usize::try_from(G::Scalar::NUM_BITS).unwrap() + (4 * i),
      },
      Variable::CG {
        commitment: 0,
        index: usize::try_from(G::Scalar::NUM_BITS).unwrap() + (4 * i) + 1,
      },
      Variable::CG {
        commitment: 0,
        index: usize::try_from(G::Scalar::NUM_BITS).unwrap() + (4 * i) + 2,
      },
      Variable::CG {
        commitment: 0,
        index: usize::try_from(G::Scalar::NUM_BITS).unwrap() + (4 * i) + 3,
      },
    )
  }
  fn two_bit_table_product(i: usize) -> Variable {
    debug_assert!(i < usize::from(u8::from((G::Scalar::NUM_BITS % 3) == 2)));
    Variable::CG {
      commitment: 0,
      index: usize::try_from(G::Scalar::NUM_BITS).unwrap() +
        (4 * usize::try_from(G::Scalar::NUM_BITS / 3).unwrap()) +
        i,
    }
  }
  fn Y_g_bold_i() -> usize {
    usize::try_from(
      G::Scalar::NUM_BITS +
        (4 * (G::Scalar::NUM_BITS / 3)) +
        u32::from(u8::from((G::Scalar::NUM_BITS % 3) == 2)),
    )
    .unwrap()
  }
  fn commit<C: Clone + Ciphersuite<F = G::FieldElement>>(
    rng: &mut impl CryptoRng,
    scalar: &G::Scalar,
  ) -> Zeroizing<PedersenVectorCommitment<C>> {
    /*
      TODO: The following is the relevant part of this circuit for this claim. We don't currently
      implement this, as this PoC exists to evaluate the signing protocol and simply defers to a
      trusted setup for the key generation protocol. For the key generation protocol to be
      implemented, this commitment would need to be paired with a proof it's well-formed of the
      following structure.

      An additional claim would also be needed the discrete logarithm is not congruent to zero
      modulo the order of the embedded elliptic curve (`s`). This would be checking that if `s_i` is
      `0`, `(less == 1) || (k_i == 0)`. If `s_i` is `1`, then `less = less || (k_i == 0)`, where `i`
      is iterated from `0` to `l`.
    */

    /*
      let mut bits = Vec::with_capacity(F::NUM_BITS.try_into().unwrap());
      for _ in 0 .. F::NUM_BITS {
        let (a, b, c) = circuit.mul(None, None, bit_iter.as_mut().map(|iter| iter.next().unwrap()));
        // a - 1 == b
        circuit.equality(LinComb::from(a).constant(-C::F::ONE), &b.into());
        // c == 0
        circuit.constrain_equal_to_zero(c.into());
        // Push the constrained bit to the result
        bits.push(a);
      }

      let mut product = |a: &Variable, b: &Variable| {
        let a = LinComb::empty().term(C::F::ONE, *a);
        let b = LinComb::empty().term(C::F::ONE, *b);
        let witness = circuit.eval(&a).map(|a| {
          let b = circuit.eval(&b).unwrap();
          (a, b)
        });
        let (_b_1, _b_2, product) = circuit.mul(Some(a), Some(b), witness);
        product
      };

      let mut three_bit_table_products = Vec::with_capacity(bits.len() / 3);
      {
        let mut iter = bits.iter();
        while let Some(_b_0) = iter.next() {
          let Some(b_1) = iter.next() else { continue };
          let Some(b_2) = iter.next() else { continue };
          three_bit_table_products.push(product(b_1, b_2));
        }
      }

      let mut two_bit_table_products = None;
      {
        let mut iter = bits.iter().skip(3 * three_bit_table_products.len());
        while let Some(b_0) = iter.next() {
          debug_assert!(two_bit_table_products.is_none());
          let Some(b_1) = iter.next() else { continue };
          two_bit_table_products = Some(product(b_0, b_1));
        }
      }
    */

    let mut values = Vec::with_capacity(usize::try_from(1 + (2 * G::Scalar::NUM_BITS)).unwrap());
    for bit in crate::const_to_le_bits(scalar) {
      values.push(C::F::conditional_select(&C::F::ZERO, &C::F::ONE, bit));
    }
    let mut bits = crate::const_to_le_bits(scalar);
    while let Some(b_0) = bits.next() {
      let Some(b_1) = bits.next() else { continue };
      if let Some(b_2) = bits.next() {
        // The 3-bit table bit preprocesses
        values.push(C::F::conditional_select(&C::F::ZERO, &C::F::ONE, b_0 & b_1));
        values.push(C::F::conditional_select(&C::F::ZERO, &C::F::ONE, b_0 & b_2));
        values.push(C::F::conditional_select(&C::F::ZERO, &C::F::ONE, b_1 & b_2));
        values.push(C::F::conditional_select(&C::F::ZERO, &C::F::ONE, b_0 & b_1 & b_2));
      } else {
        // The 2-bit table bit preprocess
        values.push(C::F::conditional_select(&C::F::ZERO, &C::F::ONE, b_0 & b_1));
      }
    }
    // The value which will be used by the nonce
    values.push(C::F::ZERO);
    Zeroizing::new(PedersenVectorCommitment { g_values: values, mask: C::F::random(rng) })
  }
}

// Equation 13
#[allow(non_camel_case_types)]
struct Delta_i<G: EmbeddedCurve>(Vec<(G::FieldElement, G::FieldElement)>);
impl<G: EmbeddedCurve> Delta_i<G> {
  fn new(C: &[G], C_xy: &CXY<G::FieldElement>, X: &[G]) -> Self {
    // For each 3-bit window, we preprocess indexes (000, 001, 010, 011, 100, 101, 110, 111)
    // For any 2-bit window after, we preprocess indexes (00, 01, 10, 11)
    // For any 1-bit window after, we preprocess indexes (0, 1)
    let three_bit_windows = usize::try_from(G::Scalar::NUM_BITS / 3).unwrap();
    let two_bit_windows = usize::from(u8::from((G::Scalar::NUM_BITS % 3) == 2));
    let one_bit_windows = usize::from(u8::from((G::Scalar::NUM_BITS % 3) == 1));
    let points = (2usize.pow(3) * three_bit_windows) +
      (2usize.pow(2) * two_bit_windows) +
      (2usize.pow(1) * one_bit_windows);
    let mut res = Vec::with_capacity(points);

    let mut populate = |prior_windows, windows, window_size, start_index| {
      for i in 0 .. windows {
        let mut last = C[prior_windows + i];
        res.push(C_xy.0[prior_windows + i]);
        for _ in 1 .. 2usize.pow(window_size) {
          let this: G = last + X[start_index + (usize::try_from(window_size).unwrap() * i)];
          res.push(this.to_xy().unwrap());
          last = this;
        }
      }
    };
    populate(0, three_bit_windows, 3, 0);
    populate(three_bit_windows, two_bit_windows, 2, 3 * three_bit_windows);
    populate(
      three_bit_windows + two_bit_windows,
      one_bit_windows,
      1,
      (3 * three_bit_windows) + (2 * two_bit_windows),
    );
    debug_assert_eq!(C_xy.0.len(), three_bit_windows + two_bit_windows + one_bit_windows);
    debug_assert_eq!(C.len(), three_bit_windows + two_bit_windows + one_bit_windows);
    debug_assert_eq!(res.len(), points);
    Self(res)
  }

  fn last_bit(&self, k_last: Variable) -> (LinComb<G::FieldElement>, LinComb<G::FieldElement>) {
    let if_zero = self.0.len() - 2;
    let if_one = if_zero + 1;
    let (x_if_0, y_if_0) = self.0[if_zero];
    let (x_if_1, y_if_1) = self.0[if_one];

    let x = LinComb::empty().constant(x_if_0).term(x_if_1 - x_if_0, k_last);
    let y = LinComb::empty().constant(y_if_0).term(y_if_1 - y_if_0, k_last);
    (x, y)
  }

  fn last_two_bits(&self) -> (LinComb<G::FieldElement>, LinComb<G::FieldElement>) {
    let two_bit_window_bits_index = usize::try_from(G::Scalar::NUM_BITS - 2).unwrap();
    let b_0 = DiscreteLogarithm::<G>::bit(two_bit_window_bits_index);
    let b_1 = DiscreteLogarithm::<G>::bit(two_bit_window_bits_index + 1);
    let b_01 = DiscreteLogarithm::<G>::two_bit_table_product(0);

    // If (b_0, b_1) == (0, 0), this yields w
    // If (b_0, b_1) == (1, 0), this yields w + x - w = x
    // If (b_0, b_1) == (0, 1), this yields w + y - w = y
    // If (b_0, b_1) == (1, 1), this yields w + x - w + y - w + z - x - y + w = z
    let select = |w, x, y, z| {
      LinComb::empty().constant(w).term(x - w, b_0).term(y - w, b_1).term(z - x - y + w, b_01)
    };

    let three_bit_windows = usize::try_from(G::Scalar::NUM_BITS / 3).unwrap();
    let index_within_vec = 2usize.pow(3) * three_bit_windows;
    let (x_00, y_00) = self.0[index_within_vec];
    let (x_01, y_01) = self.0[index_within_vec + 1];
    let (x_10, y_10) = self.0[index_within_vec + 2];
    let (x_11, y_11) = self.0[index_within_vec + 3];
    let x = select(x_00, x_01, x_10, x_11);
    let y = select(y_00, y_01, y_10, y_11);
    (x, y)
  }

  fn three_bit_table(
    &self,
    three_bit_window_i: usize,
  ) -> (LinComb<G::FieldElement>, LinComb<G::FieldElement>) {
    let b_0 = DiscreteLogarithm::<G>::bit(3 * three_bit_window_i);
    let b_1 = DiscreteLogarithm::<G>::bit((3 * three_bit_window_i) + 1);
    let b_2 = DiscreteLogarithm::<G>::bit((3 * three_bit_window_i) + 2);
    let (b_01, b_02, b_12, b_012) =
      DiscreteLogarithm::<G>::three_bit_table_products(three_bit_window_i);

    /*
      If (b_0, b_1, b_2) == (0, 0, 0), this yields w
      If (b_0, b_1, b_2) == (1, 0, 0), this yields w + x - w = x
      If (b_0, b_1, b_2) == (0, 1, 0), this yields w + y - w = y
      If (b_0, b_1, b_2) == (1, 1, 0), this yields w + x - w + y - w + z - x - y + w = z
      If (b_0, b_1, b_2) == (0, 0, 1), this yields w + l - w = l
      If (b_0, b_1, b_2) == (1, 0, 1), this yields w + x - w + l - w + m - x - l + w = m
      If (b_0, b_1, b_2) == (0, 1, 1), this yields w + y - w + l - w + n - y - l + w = n
      If (b_0, b_1, b_2) == (1, 1, 1), this yields
        w + x - w + y - w + z - x - y + w + l - w + m - x - l + w + n - y - l + w
        + o - z + x -m + l - w - n + y = o
      This same table can be achieved with `b_0, b_1, b_2, b_12`, and a per-table derivative,
      but this is paid for in the setup and offers the cheapest invocation.

      TODO: At this point, where we have 3 bits and 4 products, we can just publish eight elements
      where the `i`th element is 1 if the number is `i` and the rest are 0. We have the space in
      the vector commitment.
    */
    type F<G> = <G as EmbeddedCurve>::FieldElement;
    let select = |w: F<G>, x: F<G>, y: F<G>, z: F<G>, l: F<G>, m: F<G>, n: F<G>, o: F<G>| {
      LinComb::empty()
        .constant(w)
        .term(x - w, b_0)
        .term(y - w, b_1)
        .term(z - x - y + w, b_01)
        .term(l - w, b_2)
        .term(m - x - l + w, b_02)
        .term(n - y - l + w, b_12)
        .term(o - z + x - m + l - w - n + y, b_012)
    };

    let index_within_vec = 2usize.pow(3) * three_bit_window_i;
    let (x_000, y_000) = self.0[index_within_vec];
    let (x_001, y_001) = self.0[index_within_vec + 1];
    let (x_010, y_010) = self.0[index_within_vec + 2];
    let (x_011, y_011) = self.0[index_within_vec + 3];
    let (x_100, y_100) = self.0[index_within_vec + 4];
    let (x_101, y_101) = self.0[index_within_vec + 5];
    let (x_110, y_110) = self.0[index_within_vec + 6];
    let (x_111, y_111) = self.0[index_within_vec + 7];
    let x = select(x_000, x_001, x_010, x_011, x_100, x_101, x_110, x_111);
    let y = select(y_000, y_001, y_010, y_011, y_100, y_101, y_110, y_111);
    (x, y)
  }
}

// Equation 10
#[allow(non_camel_case_types)]
struct P_iIterator<'a, G: EmbeddedCurve> {
  C: &'a [G],
  X: &'a [G],
  iter: core::iter::Enumerate<crate::ToLeBits<G::Scalar>>,
  last: Zeroizing<G>,
}
impl<'a, G: EmbeddedCurve> P_iIterator<'a, G> {
  fn new(C: &'a [G], X: &'a [G], k: &G::Scalar) -> Self {
    Self { C, X, iter: crate::const_to_le_bits(k).enumerate(), last: Zeroizing::new(G::identity()) }
  }
}
impl<G: EmbeddedCurve> Iterator for P_iIterator<'_, G> {
  type Item = Zeroizing<G>;
  fn next(&mut self) -> Option<Self::Item> {
    let (i, b_0) = self.iter.next()?;
    let b_1 = self.iter.next();
    let b_2 = self.iter.next();

    let mut delta_i =
      Zeroizing::new(self.C[i / 3] + G::conditional_select(&G::identity(), &self.X[i], b_0));
    if let Some((i_plus_one, b_1)) = b_1 {
      *delta_i += G::conditional_select(&G::identity(), &self.X[i_plus_one], b_1);
    }
    if let Some((i_plus_two, b_2)) = b_2 {
      *delta_i += G::conditional_select(&G::identity(), &self.X[i_plus_two], b_2);
    }
    #[allow(clippy::let_and_return)]
    let res = if i == 0 {
      let P_0 = delta_i;
      P_0
    } else {
      let P_i = Zeroizing::new(*self.last + *delta_i);
      P_i
    };
    *self.last = *res;
    Some(res)
  }
}

// Claim 2
struct P;
impl P {
  fn evaluate<
    C: Clone + Ciphersuite<F: FromUniformBytes<64>>,
    G: EmbeddedCurve<FieldElement = C::F>,
  >(
    circuit: &mut Circuit<C>,
    C: &[G],
    X: &[G],
    delta_i: &Delta_i<G>,
    k: Option<&G::Scalar>,
  ) -> Variable {
    let windows = (G::Scalar::NUM_BITS / 3) + u32::from(u8::from((G::Scalar::NUM_BITS % 3) != 0));

    // "First, for i = 1,...l, verify that the point P_i ... is a point"
    let res = {
      let mut P_i =
        k.map(|k| P_iIterator::new(C, X, k).skip(1).map(|point| point.to_xy().unwrap()));
      let mut res = Vec::with_capacity((windows - 1).try_into().unwrap());
      for _ in 1 .. windows {
        let P_i = P_i.as_mut().map(|iter| iter.next().unwrap());
        // Calculate x**2
        let (x, other_x, x2) = circuit.mul(None, None, P_i.map(|(x, _y)| (x, x)));
        circuit.equality(x.into(), &other_x.into());
        // Calculate x**3
        let (_a, _b, x3) =
          circuit.mul(Some(x2.into()), Some(x.into()), P_i.map(|(x, _y)| (x * x, x)));
        // Calculate y**2
        let (y, other_y, y2) = circuit.mul(None, None, P_i.map(|(_, y)| (y, y)));
        circuit.equality(y.into(), &other_y.into());
        // Constrain y**2 = x**3 + ax + b
        circuit.equality(y2.into(), &LinComb::from(x3).term(G::a(), x).constant(G::b()));
        res.push((x, y));
      }
      debug_assert!(P_i.as_mut().map(|iter| iter.next().is_none()).unwrap_or(true));
      res
    };

    // "verify that P_0 is constructed correctly, and this is done using (13)"
    let P_0 = {
      const {
        assert!(G::Scalar::NUM_BITS >= 3);
      }
      let (delta_0_x, delta_0_y) = delta_i.three_bit_table(0);
      let witness = circuit.eval(&delta_0_x).map(|a| {
        let b = circuit.eval(&delta_0_y).unwrap();
        (a, b)
      });
      // We don't need their product, solely that they're committed to and constrained
      let (x, y, _c) = circuit.mul(Some(delta_0_x), Some(delta_0_y), witness);
      (x, y)
    };

    // "Second, for i = 1,...,l, verify that the points ... are co-linear"
    for window_i in 1 .. usize::try_from(windows).unwrap() {
      let P_i_minus_1 = if window_i == 1 { P_0 } else { res[window_i - 2] };
      let P_i = res[window_i - 1];

      let bit_i = 3 * window_i;
      let (delta_i_x, delta_i_y) =
        match usize::try_from(G::Scalar::NUM_BITS).unwrap().checked_sub(bit_i) {
          Some(0) | None => unreachable!(),
          Some(1) => delta_i.last_bit(DiscreteLogarithm::<G>::bit(bit_i)),
          Some(2) => delta_i.last_two_bits(),
          Some(_) => delta_i.three_bit_table(window_i),
        };

      // Equation 14
      let lhs = {
        let lhs_a = LinComb::from(P_i_minus_1.1).term(C::F::ONE, P_i.1);
        let lhs_b = delta_i_x.term(-C::F::ONE, P_i.0);
        let witness = circuit.eval(&lhs_a).map(|a| {
          let b = circuit.eval(&lhs_b).unwrap();
          (a, b)
        });
        let (_a, _b, lhs) = circuit.mul(Some(lhs_a), Some(lhs_b), witness);
        lhs
      };
      let rhs = {
        let rhs_a = delta_i_y.term(C::F::ONE, P_i.1);
        let rhs_b = LinComb::from(P_i_minus_1.0).term(-C::F::ONE, P_i.0);
        let witness = circuit.eval(&rhs_a).map(|a| {
          let b = circuit.eval(&rhs_b).unwrap();
          (a, b)
        });
        let (_a, _b, rhs) = circuit.mul(Some(rhs_a), Some(rhs_b), witness);
        rhs
      };
      circuit.equality(lhs.into(), &rhs.into());
    }

    // Return the x coordinate of the final point
    res.last().unwrap().0
  }
}

/*
  This circuit is universal to all invocations *for the specified points*. We take advantage of
  this to minimize verification time by simply cloning (not rebuilding) this whenever we have a new
  instance.

  Unfortunately, the underlying circuit abstraction fundamentally insists on being either the
  prover or the verifier. This means the prover must do `CommonCircuit::new(..., Some(k))` and the
  verifier must do `CommonCircuit::new(..., None)`, unable to share those builds. To minimize the
  pain of this, we preprocess all of the elliptic curve operations before `CommonCircuit::new`.
  This means we only duplicate the allocation/formatting of the constraints themselves.
*/
#[derive(Clone)]
struct CommonCircuit<
  C: Clone + Ciphersuite<F: FromUniformBytes<64>>,
  G: EmbeddedCurve<FieldElement = C::F>,
>(Circuit<C>, Variable, Variable, PhantomData<G>);
impl<C: Clone + Ciphersuite<F: FromUniformBytes<64>>, G: EmbeddedCurve<FieldElement = C::F>>
  CommonCircuit<C, G>
{
  fn new(
    C: &[G],
    X_0: &[G],
    X_0_delta_i: &Delta_i<G>,
    X_1: &[G],
    X_1_delta_i: &Delta_i<G>,
    mut circuit: Circuit<C>,
    k: Option<&G::Scalar>,
  ) -> Self {
    let dh_x_0_x = P::evaluate(&mut circuit, C, X_0, X_0_delta_i, k);
    let dh_x_1_x = P::evaluate(&mut circuit, C, X_1, X_1_delta_i, k);

    Self(circuit, dh_x_0_x, dh_x_1_x, PhantomData)
  }

  // Bind this common circuit to a specific instance
  fn bind(self, k_apostrophe: C::F) -> Circuit<C> {
    let Self(mut circuit, dh_x_0_x, dh_x_1_x, PhantomData) = self;
    circuit.equality(
      LinComb::from(dh_x_1_x).term(k_apostrophe, dh_x_0_x),
      &LinComb::from(Variable::CG { commitment: 0, index: DiscreteLogarithm::<G>::Y_g_bold_i() }),
    );
    circuit
  }
}

/// The global setup for the DDH eVRF.
#[derive(Clone)]
pub struct DdhEvrfGlobalSetup<
  C: Clone + Ciphersuite<F: FromUniformBytes<64>>,
  G: EmbeddedCurve<FieldElement = C::F>,
> {
  generators: Generators<C>,
  C: Vec<G>,
  C_xy: CXY<G::FieldElement>,
}

/// The view of a setup for the DDH eVRF.
/*
  We use a slightly modified setup from $Q, k', \pi_Q$ to $Q_{lo}, Q_{hi}$. We derive $k'$ as the
  hash of $Q_{lo}, Q_{hi}$, which is a uniform value effectively random yet without communication
  overhead. We drop $\pi_Q$ as $\pi_Q$ is necessary when $Q$ is intended to be over a single
  generator for its later summation into a Pedersen Vector Commitment. As extensively described
  above, we don't use our $Q_{lo}, Q_{hi}$ values as such. Our Bulletproofs do assert they're
  well-formed without risk of side effects (as they are treated as independent Pedersen
  Commitments). While the prover may perform the setup with a $Q_{lo}, Q_{hi}$ they cannot open,
  they could already so by committing to a $k$ value greater than or equal to $2**ceil_log_2(s)$.
*/
#[derive(Clone)]
pub struct DdhEvrfSetupView<C: Clone + Ciphersuite> {
  Q: C::G,
  k_apostrophe: C::F,
}
impl<C: Clone + Ciphersuite<F: FromUniformBytes<64>>> DdhEvrfSetupView<C> {
  fn new(Q: C::G) -> Self {
    let k_apostrophe = C::F::from_uniform_bytes(&{
      let mut hasher = blake3::Hasher::new();
      hasher.update(Q.to_bytes().as_ref());
      let mut bytes = [0; 64];
      hasher.finalize_xof().fill(&mut bytes);
      bytes
    });

    DdhEvrfSetupView { Q, k_apostrophe }
  }
}

/// A setup for the eVRF.
#[derive(Clone)]
pub struct DdhEvrfSetup<
  C: Clone + Ciphersuite<F: FromUniformBytes<64>>,
  G: EmbeddedCurve<FieldElement = C::F>,
> {
  k: Zeroizing<G::Scalar>,
  Q: Zeroizing<PedersenVectorCommitment<C>>,
  Q_commitment: C::G,
  k_apostrophe: C::F,
}

/// The context for the DDH eVRF.
pub struct DdhEvrfContext<
  C: Clone + Ciphersuite<F: FromUniformBytes<64>>,
  G: EmbeddedCurve<FieldElement = C::F>,
> {
  X_0: Vec<G>,
  X_0_delta_i: Delta_i<G>,
  X_1: Vec<G>,
  X_1_delta_i: Delta_i<G>,
  verifier_circuit: CommonCircuit<C, G>,
}

fn random_point<G: GroupEncoding>(xof: &mut blake3::OutputReader) -> G {
  loop {
    let mut bytes = G::Repr::default();
    xof.fill(bytes.as_mut());
    if let Some(point) = Option::<G>::from(G::from_bytes(&bytes)) {
      break point;
    }
  }
}

/// The DDH-premised eVRF proposed within the eVRF paper.
pub struct DdhEvrf<
  C: Clone + Ciphersuite<F: FromUniformBytes<64>>,
  G: EmbeddedCurve<FieldElement = C::F>,
>(PhantomData<(C, G)>);
impl<
  CG: class_groups::Element,
  P: Parameters<CG>,
  C: Clone + Ciphersuite<G = P::E, F = P::F>,
  G: EmbeddedCurve<FieldElement = C::F>,
> Evrf<CG, P> for DdhEvrf<C, G>
{
  type GlobalSetup = DdhEvrfGlobalSetup<C, G>;
  type SetupView = DdhEvrfSetupView<C>;
  type Setup = DdhEvrfSetup<C, G>;
  type Context = DdhEvrfContext<C, G>;
  type BatchVerifier = BatchVerifier<C>;

  fn global_setup() -> Self::GlobalSetup {
    let Y_g_bold_i = DiscreteLogarithm::<G>::Y_g_bold_i();
    let generators = {
      let mut xof = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"DDH eVRF Generators");
        hasher.finalize_xof()
      };
      let g = random_point::<C::G>(&mut xof);
      let h = random_point::<C::G>(&mut xof);
      // TODO: Properly calculate this instead of this estimation which does work
      let generators = usize::try_from((4 * G::Scalar::NUM_BITS).next_power_of_two()).unwrap();
      let mut g_bold = Vec::with_capacity(generators);
      let mut h_bold = Vec::with_capacity(generators);
      for _ in 0 .. generators {
        g_bold.push(random_point::<C::G>(&mut xof));
        h_bold.push(random_point::<C::G>(&mut xof));
      }
      // Set the Pedersen Vector Commitment we use for the nonce to the generator used for ECDSA
      g_bold[Y_g_bold_i] = C::G::generator();
      Generators::new(g, h, g_bold, h_bold).unwrap()
    };
    let C = C::<G>();
    let C_xy = CXY::new::<G>(&C);

    DdhEvrfGlobalSetup { generators, C, C_xy }
  }

  fn setup(
    global_setup: &Self::GlobalSetup,
    rng: &mut impl CryptoRng,
  ) -> (Self::SetupView, Self::Setup) {
    let k = loop {
      let candidate = Zeroizing::new(G::Scalar::random(&mut *rng));
      // Negligible probability yet would be invalid
      if bool::from(candidate.is_zero()) {
        continue;
      }
      break candidate;
    };

    let Q = DiscreteLogarithm::<G>::commit(rng, &k);
    let setup_view = DdhEvrfSetupView::new(
      Q.commit(global_setup.generators.g_bold_slice(), global_setup.generators.h()).unwrap(),
    );
    let setup =
      DdhEvrfSetup { k, Q, Q_commitment: setup_view.Q, k_apostrophe: setup_view.k_apostrophe };
    (setup_view, setup)
  }

  fn context(global_setup: &Self::GlobalSetup, transcript: &mut blake3::Hasher) -> Self::Context {
    let mut xof = transcript.finalize_xof();
    transcript.update(&[0]);

    let one_X_0 = random_point::<G>(&mut xof);
    let one_X_1 = random_point::<G>(&mut xof);

    let mut X_0 = Vec::with_capacity(G::Scalar::NUM_BITS.try_into().unwrap());
    X_0.push(one_X_0);
    let mut X_1 = Vec::with_capacity(G::Scalar::NUM_BITS.try_into().unwrap());
    X_1.push(one_X_1);
    for _ in 1 ..= G::Scalar::CAPACITY {
      let two_i_X_0 = X_0.last().unwrap().double();
      X_0.push(two_i_X_0);

      let two_i_X_1 = X_1.last().unwrap().double();
      X_1.push(two_i_X_1);
    }

    let X_0_delta_i = Delta_i::new(&global_setup.C, &global_setup.C_xy, &X_0);
    let X_1_delta_i = Delta_i::new(&global_setup.C, &global_setup.C_xy, &X_1);
    let verifier_circuit = CommonCircuit::new(
      &global_setup.C,
      &X_0,
      &X_0_delta_i,
      &X_1,
      &X_1_delta_i,
      Circuit::verify(),
      None,
    );
    DdhEvrfContext { X_0, X_0_delta_i, X_1, X_1_delta_i, verifier_circuit }
  }

  fn prove<W: io::Write>(
    rng: &mut impl CryptoRng,
    global_setup: &Self::GlobalSetup,
    setup: &Self::Setup,
    context: &Self::Context,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<Zeroizing<P::F>> {
    let ecdh_0 = Zeroizing::new(Zeroizing::new(context.X_0[0] * setup.k.deref()).to_xy().unwrap());
    let ecdh_1 = Zeroizing::new(Zeroizing::new(context.X_1[0] * setup.k.deref()).to_xy().unwrap());
    let nonce = Zeroizing::new((ecdh_0.deref().0 * setup.k_apostrophe) + ecdh_1.deref().0);

    let Y = P::E::generator() * nonce.deref();
    transcript.write_all(Y.to_bytes().as_ref())?;

    // Prove the opening of Y
    {
      let r_nonce = Zeroizing::new(C::F::random(&mut *rng));
      transcript.write_all((P::E::generator() * r_nonce.deref()).to_bytes().as_ref())?;
      let c = P::from_xof(transcript.0.finalize_xof());
      transcript.write_all(((c * nonce.deref()) + r_nonce.deref()).to_repr().as_ref())?;
    }

    let mut T = setup.Q.deref().clone();
    T.g_values[DiscreteLogarithm::<G>::Y_g_bold_i()] = *nonce;

    let circuit = CommonCircuit::new(
      &global_setup.C,
      &context.X_0,
      &context.X_0_delta_i,
      &context.X_1,
      &context.X_1_delta_i,
      Circuit::prove(vec![T], vec![]),
      Some(&setup.k),
    )
    .bind(setup.k_apostrophe);
    let muls = circuit.muls();

    let mut bp_transcript = transcript::Transcript::new(transcript.0.finalize().into());
    let commitments = bp_transcript.write_commitments::<C>(vec![setup.Q_commitment + Y], vec![]);

    let (statement, witness) = circuit
      .statement(global_setup.generators.reduce(muls.next_power_of_two()).unwrap(), commitments)
      .unwrap();
    let witness = witness.unwrap();
    statement.prove(&mut *rng, &mut bp_transcript, witness).unwrap();
    let bp = bp_transcript.complete();
    // Write everything after $T$
    transcript.write_all(&bp[<C::G as GroupEncoding>::Repr::default().as_ref().len() ..])?;

    Ok(nonce)
  }

  fn batch_verifier(_global_setup: &Self::GlobalSetup) -> Self::BatchVerifier {
    Generators::batch_verifier()
  }
  fn queue_verification<R: io::Read>(
    rng: &mut impl CryptoRng,
    global_setup: &Self::GlobalSetup,
    global_batch_verifier: &mut Self::BatchVerifier,
    // TODO: Use this to implement identifiable aborts
    _participant: dkg::Participant,
    setup: &Self::SetupView,
    context: &Self::Context,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<P::E> {
    // The GBP lib will corrupt its batch verifier on error, so we clone it here
    let mut batch_verifier = BatchVerifier {
      g: global_batch_verifier.g,
      h: global_batch_verifier.h,
      g_bold: global_batch_verifier.g_bold.clone(),
      h_bold: global_batch_verifier.h_bold.clone(),
      h_sum: global_batch_verifier.h_sum.clone(),
      additional: global_batch_verifier.additional.clone(),
    };

    // The commitment for the nonce
    let Y = P::read_canonical_E(&mut *transcript)?;

    // Read the PoK for the nonce
    let R_nonce = P::read_canonical_E(&mut *transcript)?;
    let Y_c = P::from_xof(transcript.0.finalize_xof());
    let s_nonce = C::read_F(&mut *transcript)?;

    let circuit = context.verifier_circuit.clone().bind(setup.k_apostrophe);
    let muls = circuit.muls();

    let bp_context = transcript.0.finalize().into();

    let point_len = <C::G as GroupEncoding>::Repr::default().as_ref().len();
    let bp_len = {
      let scalar_len = <C::F as PrimeField>::Repr::default().as_ref().len();

      debug_assert_eq!(2u8.next_power_of_two(), 2);
      debug_assert_eq!(2u8.ilog2(), 1);
      // (T, (A_I, A_O, S), (T_0, T_1, T_3, T_4, T_5, T_6), (L_i, R_i))
      /*
        Please note we read $T_0$ from the transcript, when Bulletproofs doesn't, as Bulletproofs
        assumes it's zero yet Generalized Bulletproofs doesn't (as it's non-zero when using
        Pedersen Vector Commitments).
      */
      let points = 1 + 3 + 6 + (2 * usize::try_from(muls.next_power_of_two().ilog2()).unwrap());
      // (tau_x, u, \hat{t}, a, b)
      let scalars = 5;
      (points * point_len) + (scalars * scalar_len)
    };
    let mut bp = vec![0; bp_len];
    bp[.. point_len].copy_from_slice((setup.Q + Y).to_bytes().as_ref());
    transcript.read_exact(&mut bp[point_len ..])?;

    let mut bp_transcript = transcript::VerifierTranscript::new(bp_context, &bp);
    let commitments = bp_transcript.read_commitments(1, 0)?;
    circuit
      .statement(global_setup.generators.reduce(muls).unwrap(), commitments)
      .unwrap()
      .0
      .verify(&mut *rng, &mut batch_verifier, &mut bp_transcript)
      .map_err(|e| io::Error::other(format!("{e:?}")))?;

    // Verify the PoK for the nonce
    {
      let weight = C::F::random(&mut *rng);
      // R
      batch_verifier.additional.push((weight, R_nonce));
      // + cX
      batch_verifier.additional.push((weight * Y_c, Y));
      // - sG == 0
      batch_verifier.g_bold[DiscreteLogarithm::<G>::Y_g_bold_i()] -= weight * s_nonce;
    }

    // Since we didn't error (corrupting the batch verifier), write this back to the global batch
    // verifier
    *global_batch_verifier = batch_verifier;

    Ok(Y)
  }
  fn verify(
    global_setup: &Self::GlobalSetup,
    batch_verifier: Self::BatchVerifier,
  ) -> Result<(), Vec<dkg::Participant>> {
    if !global_setup.generators.verify(batch_verifier) {
      todo!("TODO");
    }
    Ok(())
  }
}

#[test]
fn test_ddh_evrf() {
  use rand::{rand_core, rngs::SysRng};

  type EvrfInstantiated = DdhEvrf<ciphersuite_kp256::Secp256k1, secq256k1::Point>;
  type Parameters = crate::Secp256k1<crate::CryptoPrimesStackCcykc>;
  type Element = class_groups::CryptoBigintStackElement;

  let global_setup = <EvrfInstantiated as Evrf<Element, Parameters>>::global_setup();

  let (setup_view, setup) = <EvrfInstantiated as Evrf<Element, Parameters>>::setup(
    &global_setup,
    &mut rand_core::UnwrapErr(SysRng),
  );

  let context = <EvrfInstantiated as Evrf<Element, Parameters>>::context(
    &global_setup,
    &mut blake3::Hasher::new(),
  );

  let mut transcript = DigestWriter(blake3::Hasher::new(), vec![]);
  let nonce = <EvrfInstantiated as Evrf<Element, Parameters>>::prove(
    &mut rand_core::UnwrapErr(SysRng),
    &global_setup,
    &setup,
    &context,
    &mut transcript,
  )
  .unwrap();

  let mut batch_verifier =
    <EvrfInstantiated as Evrf<Element, Parameters>>::batch_verifier(&global_setup);
  let mut transcript = DigestReader(blake3::Hasher::new(), transcript.1.as_slice());
  let nonce_commitment = <EvrfInstantiated as Evrf<Element, Parameters>>::queue_verification(
    &mut rand_core::UnwrapErr(SysRng),
    &global_setup,
    &mut batch_verifier,
    dkg::Participant::new(1).unwrap(),
    &setup_view,
    &context,
    &mut transcript,
  )
  .unwrap();
  assert_eq!(k256::ProjectivePoint::GENERATOR * *nonce, nonce_commitment);
  <EvrfInstantiated as Evrf<Element, Parameters>>::verify(&global_setup, batch_verifier).unwrap();
}
