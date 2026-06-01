use core::ops::Neg;

use rug::{*, integer::Order};

/// An element of a class group, implemented with the variable-time gmp.
///
/// This requires linking to `gmp`, written in C. It is faster than the pure-Rust
/// `MalachiteElement` and accordingly preferable on eligible platforms.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GmpElement {
  a: Integer,
  b: Integer,
  c: Integer,
  L: Integer,
}

impl GmpElement {
  // Algorithm 5.4.2 of A Course in Computational Algebraic Number Theory
  fn reduce(self) -> Self {
    let Self { mut a, mut b, mut c, L } = self;

    // Step 2
    let normalize = |a: &mut Integer, b: &mut Integer, c: &mut Integer| {
      let two_a = a.clone() << 1;
      let (mut q, mut r) = b.div_rem_euc_ref(&two_a).complete();
      if r > *a {
        r -= two_a;
        q += Integer::ONE;
      }
      *c -= ((b.clone() + &r) * q) >> 1;
      *b = r;
    };

    // Step 1
    if !((-a.clone() < b) && (b <= a)) {
      // Step 2
      normalize(&mut a, &mut b, &mut c);
    }
    // Step 3, first sentence
    while a > c {
      std::mem::swap(&mut a, &mut c);
      b = -b;
      // Go to step 2
      normalize(&mut a, &mut b, &mut c);
    }
    // Step 3, second sentence
    if (a == c) && b.is_negative() {
      b = -b;
    }

    debug_assert!(b.clone().abs() <= a.clone());
    debug_assert!(a.clone() <= c.clone());
    debug_assert!(if (b.clone().abs() == a.clone()) || (a.clone() == c.clone()) {
      !b.is_negative()
    } else {
      true
    });
    Self { a, b, c, L }
  }
}

impl crate::Element for GmpElement {
  fn is_identity(&self) -> subtle::Choice {
    u8::from((self.a == *Integer::ONE) && (self.b == *Integer::ONE)).into()
  }

  // Algorithm 5.4.8 of A Course in Computational Algebraic Number Theory
  fn double(&self) -> Self {
    let L = &self.L;

    let (d1, u, v) = self.b.clone().extended_gcd(self.a.clone(), Integer::new());
    debug_assert_eq!((u.clone() * &self.b) + (v.clone() * &self.a), d1);
    let A = self.a.clone() / &d1;
    let B = self.b.clone() / &d1;
    let mut C = -((self.c.clone() * &u) % &A);
    let C1 = A.clone() - &C;
    if C1 < C {
      C = -C1;
    }

    let parteucl = |a: Integer, b: Integer| {
      let mut v = Integer::ZERO.clone();
      let mut d = a;
      let mut v2 = Integer::ONE.clone();
      let mut v3 = b;
      let mut z = Integer::ZERO;
      while v3.clone().abs() > *L {
        let (q, t3) = d.div_rem_euc_ref(&v3).complete();
        debug_assert_eq!((q.clone() * &v3) + &t3, d);
        let t2 = v.clone() - (q.clone() * &v2);
        v = v2;
        d = v3;
        v2 = t2;
        v3 = t3;
        z += Integer::ONE;
      }
      if z.is_odd() {
        v2 = -v2;
        v3 = -v3;
      }
      (v, d, v2, v3, z)
    };

    let (mut v, d, mut v2, v3, z) = parteucl(A.clone(), C);
    if z == Integer::ZERO {
      let g = ((B.clone() * &v3) + &self.c) / &d;
      let a2 = d.clone() * &d;
      let c2 = v3.clone().square();
      let b2_part = d.clone() + &v3;
      let b2 = self.b.clone() + b2_part.square() - &a2 - &c2;
      let c2 = c2 + (g.clone() * &d1);
      return (GmpElement { a: a2, b: b2, c: c2, L: self.L.clone() }).reduce();
    }

    let e = ((self.c.clone() * &v) + (B.clone() * &d)) / &A;
    let g = ((e.clone() * &v2) - &B) / &v;
    let mut b2 = (e.clone() * &v2) + (v.clone() * &g);
    if d1 > *Integer::ONE {
      b2 *= &d1;
      v *= &d1;
      v2 *= &d1;
    }
    let a2 = d.clone() * &d;
    let c2 = v3.clone().square();
    let b2_part = d.clone() + &v3;
    let b2 = b2 + b2_part.square() - &a2 - &c2;
    let a2 = a2 + (e * &v);
    let c2 = c2 + (g * &v2);
    (GmpElement { a: a2, b: b2, c: c2, L: self.L.clone() }).reduce()
  }

  // Algorithm 5.4.9 of A Course in Computational Algebraic Number Theory
  fn add(&self, other: &Self) -> GmpElement {
    if self.is_identity().into() {
      return other.clone();
    }
    if other.is_identity().into() {
      return self.clone();
    }

    let L = &self.L;

    let (f1, f2) = if self.a < other.a { (other, self) } else { (self, other) };
    let mut s = (f1.b.clone() + &f2.b) >> 1u32;
    let n = f2.b.clone() - &s;

    let (mut d, u, v) = f2.a.clone().extended_gcd(f1.a.clone(), Integer::new());
    debug_assert_eq!((u.clone() * &f2.a) + (v.clone() * &f1.a), d);

    let mut a1 = f1.a.clone();
    let mut a2 = f2.a.clone();

    let (A, d1) = if d == *Integer::ONE {
      let A = -u * &n;
      let d1 = d;
      (A, d1)
    } else if (s.clone() % &d) == Integer::ZERO {
      let A = -u * &n;
      let d1 = d;
      a1 /= &d1;
      a2 /= &d1;
      s /= &d1;
      (A, d1)
    } else {
      let (d1, u1, _) = s.clone().extended_gcd(d.clone(), Integer::new());
      if d1 > *Integer::ONE {
        a1 /= &d1;
        a2 /= &d1;
        s /= &d1;
        d /= &d1;
      }

      let l = (u.clone() * (f1.c.clone() % &d)) + (v * (f2.c.clone() % &d));
      let l = (l * u1) % &d;
      let l = d.clone() - l;
      let A = (l * (a1.clone() / &d)) - (u * (n.clone() / &d));
      (A, d1)
    };

    let mut A = A % &a1;
    let A1 = a1.clone() - &A;
    if A1 < A {
      A = -A1;
    }

    let parteucl = |a: Integer, b: Integer| {
      let mut v = Integer::ZERO.clone();
      let mut d = a;
      let mut v2 = Integer::ONE.clone();
      let mut v3 = b;
      let mut z = Integer::ZERO;
      while v3.clone().abs() > *L {
        let (q, t3) = (d.clone() / &v3, d.clone() % &v3);
        debug_assert_eq!((q.clone() * &v3) + &t3, d);
        let t2 = v - (q.clone() * &v2);
        v = v2;
        d = v3;
        v2 = t2;
        v3 = t3;
        z += Integer::ONE;
      }
      if z.is_odd() {
        v2 = -v2;
        v3 = -v3;
      }
      (v, d, v2, v3, z)
    };

    let (mut v, d, mut v2, v3, z) = parteucl(a1.clone(), A);

    if z == Integer::ZERO {
      let Q1 = a2.clone() * &v3;
      let Q2 = Q1.clone() + &n;
      let f = Q2.clone() / &d;
      let g = ((s * &v3) + &f2.c) / &d;
      let a3 = d * &a2;
      let c3 = (v3 * &f) + (g * &d1);
      let b3 = (Q1 << 1) + &f2.b;
      return (GmpElement { a: a3, b: b3, c: c3, L: self.L.clone() }).reduce();
    }

    let b = ((a2.clone() * &d) + (n.clone() * &v)) / &a1;
    let Q1 = b.clone() * &v3;
    let Q2 = Q1.clone() + &n;
    let f = Q2.clone() / &d;
    let e = ((s.clone() * &d) + (f2.c.clone() * &v)) / &a1;
    let Q3 = e.clone() * &v2;
    let Q4 = Q3.clone() - &s;
    let g = Q4.clone() / &v;
    if d1 > *Integer::ONE {
      v2 = d1.clone() * &v2;
      v = d1.clone() * &v;
    }

    let a3 = (d * &b) + (e * &v);
    let c3 = (v3 * &f) + (g * &v2);
    let b3 = (Q1 + &Q2) + (d1 * (Q3 + &Q4));
    (GmpElement { a: a3, b: b3, c: c3, L: self.L.clone() }).reduce()
  }

  fn sub(&self, other: GmpElement) -> GmpElement {
    self.add(&-other)
  }

  // SAFETY: This always reduces forms and does return a well-defined form as required.
  unsafe fn a_b_c_discriminant(
    &self,
  ) -> (
    impl AsRef<[u8]>,
    (crypto_bigint::Choice, impl AsRef<[u8]>),
    impl AsRef<[u8]>,
    impl AsRef<[u8]>,
  ) {
    let a = self.a.to_digits::<u8>(Order::LsfLe);
    let b = (u8::from(!self.b.is_negative()).into(), self.b.to_digits::<u8>(Order::LsfLe));
    let c = self.c.to_digits::<u8>(Order::LsfLe);

    let discriminant = (((self.a.clone() * self.c.clone()) << 2u32) - self.b.clone().square())
      .to_digits::<u8>(Order::LsfLe);

    (a, b, c, discriminant)
  }

  unsafe fn from_coefficients(
    a: impl AsRef<[u8]>,
    (b_positive, b_abs): (crypto_bigint::Choice, impl AsRef<[u8]>),
    c: impl AsRef<[u8]>,
    discriminant_abs: impl AsRef<[u8]>,
  ) -> Self {
    let to_gmp = |value: &[u8]| Integer::from_digits(value, Order::LsfLe);

    let a = to_gmp(a.as_ref());

    let mut b = to_gmp(b_abs.as_ref());
    if !bool::from(b_positive) {
      b = -b;
    }

    let c = to_gmp(c.as_ref());

    // b^2 - 4ac = delta
    let delta: Integer = to_gmp(discriminant_abs.as_ref());
    let mut tess_root = delta.clone().abs().root(4);
    if tess_root.clone().square().square() < delta.abs() {
      tess_root += Integer::from(1u8);
    }

    Self { a, b, c, L: tess_root }
  }
}

impl Neg for GmpElement {
  type Output = Self;
  fn neg(self) -> Self {
    Self { a: self.a, b: -self.b, c: self.c, L: self.L.clone() }.reduce()
  }
}

impl crate::ElementExt for GmpElement {}
