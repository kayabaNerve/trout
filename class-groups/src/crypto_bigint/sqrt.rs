use crypto_bigint::{
  CtEq as _, CtAssign, Zero, One, Odd, JacobiSymbol, NegMod, MulMod, SquareMod, BitOps, Limb,
  UintRef,
};

/// The required view over a collection of limbs to calculate a square root.
trait SquareRoot:
  Clone
  + AsRef<[Limb]>
  + AsMut<[Limb]>
  + Zero
  + One
  + NegMod<Output = Self>
  + MulMod<Output = Self>
  + SquareMod<Output = Self>
  + BitOps
{
  /// Compute $self^{exp} \mod modulus$.
  ///
  /// This MUST support $self \ge mmodlus$.
  fn pow_mod(self, exp: Self, modulus: &Odd<Self>) -> Self;
}

impl<
  T: Clone
    + AsRef<[Limb]>
    + AsMut<[Limb]>
    + CtAssign
    + Zero
    + One
    + NegMod<Output = Self>
    + MulMod<Output = Self>
    + SquareMod<Output = Self>
    + BitOps,
> SquareRoot for T
{
  fn pow_mod(self, exp: Self, modulus: &Odd<Self>) -> Self {
    let mut result = Self::one_like(modulus);
    let mut square = self.clone();
    for i in 0 .. modulus.as_ref().bits_precision() {
      result.ct_assign(
        &result.mul_mod(&square, modulus.as_nz_ref()),
        u8::from(exp.bit_vartime(i)).ct_eq(&1),
      );
      square = square.square_mod(modulus.as_nz_ref());
    }
    result
  }
}

/// Calculate the Legendre symbol of `a` over the odd prime `p`.
///
/// This is equivalent to the Jacobi symbol given the requirement `p` is an odd prime (a bound
/// required for the Legendre symbol which the Jacobi symbol is a generalization of).
///
/// This assumes `p` is an odd prime. This does not require `a < p`.
///
/// This function runs in constant time (solely variable to the precision of its inputs).
#[expect(private_bounds)]
pub(crate) fn legendre_symbol<U: SquareRoot>(a: U, p: &Odd<U>) -> JacobiSymbol {
  /*
    The following is premised on Euler's criterion which states that for an odd prime `p`, where
    `a` is coprime to `p`, then $a^{(p - 1) / 2} \cong 1 \mod p$ if $a$ is quadratic residue modulo
    `p`.
  */

  let p_minus_one_div_two = {
    let mut p_minus_one_div_two = p.as_ref().clone();
    // This is known to be correct as `p` is bound to be an odd prime, meaning the
    // least-significant bit is `1` (causing the subtraction to be contained to the bit we shift
    // out)
    UintRef::new_mut(p_minus_one_div_two.as_mut()).shr1_assign();
    p_minus_one_div_two
  };

  let exponentation = a.pow_mod(p_minus_one_div_two, p);
  let (exponentation_is_zero, exponentation_is_one) = {
    let exponentation = <_ as AsRef<[Limb]>>::as_ref(&exponentation);
    let mut exponentation_is_zero = Limb::ZERO;
    for limb in exponentation.iter().skip(1) {
      exponentation_is_zero |= limb;
    }
    let mut exponentation_is_zero = exponentation_is_zero.is_zero();
    let mut exponentation_is_one = exponentation_is_zero;
    exponentation_is_zero &= exponentation[0].is_zero();
    exponentation_is_one &= exponentation[0].is_one();
    (exponentation_is_zero, exponentation_is_one)
  };

  /*
    `JacobiSymbol` does not implement `CtAssign`, so we transmute it to its underlying
    representation, `i8`, and use that instead. Note `core::mem::transmute` asserts the types are
    the same size and we do not have to consider alignment as these aren't references.
  */
  let (one, zero, minus_one) = unsafe {
    (
      core::mem::transmute::<JacobiSymbol, i8>(JacobiSymbol::One),
      core::mem::transmute::<JacobiSymbol, i8>(JacobiSymbol::Zero),
      core::mem::transmute::<JacobiSymbol, i8>(JacobiSymbol::MinusOne),
    )
  };

  let mut result = minus_one;
  result.ct_assign(&one, exponentation_is_one);
  // The exponent was non-zero (as the first odd prime is `3` and `(3 - 1) / 2 = 1`) so if
  // $a \cong 0 \mod p$, then $a^{(p - 1) / 2} \cong 0 \mod p$.
  result.ct_assign(&zero, exponentation_is_zero);

  // This is safe we know this value is valid as a `JacobiSymbol` (it being transmuted from one)
  unsafe { core::mem::transmute::<i8, JacobiSymbol>(result) }
}

/// Calculate the square root of `n` modulo the odd prime `p`.
///
/// This assumes `p` is an odd prime. This does not require `n >= p`.
///
/// The returned square root will always be the _odd_ square root.
///
/// This function runs in variable time. This function finds the least quadratic non-residue for
/// $p$, which is fixed to $p$, and a non-trivial part of the computation. This function SHOULD NOT
/// be used for square roots when the prime $p$ is consistent across multiple calls to calculate a
/// square root.
/*
  TODO: For this use case, should we implement Cipolla's algorithm? It also requires finding a
  quadratic non-residue, one bespoke to the number we're taking the square root of, so it _can't_
  be preprocessed yet we don't support preprocessing anyways. The remainder of the algorithm is
  one modular exponentation in an extension field, which is annoying but avoids a loop re: `S`.

  Cipolla's algorithm is bounded by `log_2(p)` the amount of bits in the exponent, not
  `log_2(p)^2`, the product of the complexities for the outer and inner loop which each iterate
  over `S`. It also just may be more straightforward.

  It should be noted the stronger bound doesn't matter too much when this is variable-time, and
  Tonelli-Shanks is reasonable in variable-time, and a constant time variant would need a
  termination bound for finding a quadratic non-residue (which Tonelli-Shanks can do under the
  Generalized Riemann Hypothesis, but Cipolla's algorithm could only do to a statistical bound).
*/
#[expect(private_bounds)]
pub(crate) fn sqrt_mod_p_vartime<U: SquareRoot>(n: U, p: &Odd<U>) -> Option<U> {
  match legendre_symbol(n.clone(), p) {
    JacobiSymbol::One => {}
    JacobiSymbol::Zero => return Some(U::zero_like(p.as_ref())),
    JacobiSymbol::MinusOne => return None,
  }

  /*
    The following is an implementation of the Tonelli-Shanks algorithm for finding square roots
    modulo an odd prime `p`. While the cases $p \cong 3 \mod 4$ and $p \cong 5 mod 4$ do enable
    much simpler algorithms, the following is implemented for being universal.
  */

  /*
    `S` is the amount of zero bits before the first (from least-significant to
    most-significant) set bit in `p - 1`. As `p` is an odd prime, we know the least-significant
    bit of `p - 1` is zero.
  */
  let mut S = 1;
  while !p.as_ref().bit_vartime(S) {
    S += 1;
  }

  // `Q` is $(p - 1) / 2^S$, which is an integer by the definition of `S`
  let mut Q = p.as_ref().clone();
  UintRef::new_mut(Q.as_mut()).shr_assign(S);

  // $(Q + 1) / 2$ where $Q$ is odd by construction
  let mut Q_plus_1_div_2 = Q.clone();
  {
    let limbs = <_ as AsMut<[Limb]>>::as_mut(&mut Q_plus_1_div_2);
    let mut carry = UintRef::new_mut(limbs).add_assign_limb(Limb::ONE);
    for i in (0 .. limbs.len()).rev() {
      let new_limb = (carry << (Limb::BITS - 1)) | (limbs[i] >> 1);
      carry = limbs[i] & Limb::ONE;
      limbs[i] = new_limb;
    }
    // An odd number plus one will be even, as allowing the division by two
    debug_assert!(bool::from(carry.is_zero()));
  }
  let mut R = n.clone().pow_mod(Q_plus_1_div_2, p);
  let mut t = n.pow_mod(Q.clone(), p);

  /*
    Find the least quadratic non-residue within the odd-prime field $p$.

    Every odd prime has `(p - 1) / 2` quadratic non-residues, so every odd prime has _a_ quadratic
    non-residue. This ensures the following calculation terminates and doesn't have capacity
    exceeding the capacity of the container for `p`.

    Assuming the Generalized Riemann Hypothesis, $2 \le z \le log_e(q)^2$ for $q \ge 5$.

    Corollary 1.1 of "Conditional Bounds for the Least Quadratic Non-Residue and Related Problems"
    by Youness Lamzouri, Xiannan Li, and Kannan Soundararajan.
    https://pubs.ams.org/journals/mcom/2015-84-295/S0025-5718-2015-02925-1/home.html

    As $e > 2$, $log_e(q) \le log_2(q)$, letting us replace the upper bound as so. Then, for the
    sole exceptional odd prime $q = 3$ (where $log_e(3)^2 < 2$), we do have $log_2(3)^2 \ge 2$
    (where $2$ is the least quadratic non-residue modulo $3$).

    This lets us bound (under the Generalized Riemann Hypothesis) $2 \le z \le log_2(q)^2$, where
    $z$ is the least quadratic non-residue (as we want) and $q$ is an odd prime (as our input is
    bound).

    Alternatively, if one assumes the distribution of quadratic non-residues uniform over the prime
    field, this achieves a statistical bound on termination within $(1/2)^z$ iterations.

    NOTE: We could make this function constant-time assuming the Generalized Riemann Hypothesis.
    It'd have $log_2(p)^2$ complexity however, not only to find `z` but also as the following loop
    has a runtime of $(S^2) / 2$ (where $S \le log_2(p)$).
  */
  let z = {
    let mut z = U::zero_like(p.as_ref());
    <_ as AsMut<[Limb]>>::as_mut(&mut z)[0] = Limb::from(2u8);
    while legendre_symbol(z.clone(), p) != JacobiSymbol::MinusOne {
      let _carry = UintRef::new_mut(z.as_mut()).add_assign_limb(Limb::ONE);
    }
    z
  };

  let mut M = S;
  let mut c = z.pow_mod(Q, p);

  /*
    Each iteration of this loop decreases `M` by at least one, where this loop runs for values
    $1 < M \le S$. This loop will accordingly run for $S \le log_2(p)$ iterations at most.
  */
  while !bool::from(t.is_one()) {
    let i = {
      let mut t = t.clone();
      let mut i = 0;
      // This loop will run for `M` times at most where $2 \le M \le S$ and $S \le log_2(p)$
      while !bool::from(t.is_one()) {
        i += 1;
        assert!(i < M);
        t = t.square_mod(p.as_nz_ref());
      }
      i
    };

    let mut b = c;
    for _ in 0 .. (M - i - 1) {
      b = b.square_mod(p.as_nz_ref());
    }

    M = i;
    c = b.square_mod(p.as_nz_ref());
    t = t.mul_mod(&c, p.as_nz_ref());

    R = R.mul_mod(&b, p.as_nz_ref());
  }

  // Normalize to the odd square root
  if (<_ as AsRef<[Limb]>>::as_ref(&R)[0] & Limb::ONE) != Limb::ONE {
    R = R.neg_mod(p.as_nz_ref());
  }

  Some(R)
}
