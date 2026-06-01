use core::{cmp::Ordering, ops::Neg};

use ::malachite::{
  base::num::{arithmetic::traits::*, basic::traits::*, conversion::traits::*},
  *,
};

pub(crate) fn natural_from_bytes(bytes: &[u8]) -> Natural {
  Natural::from_digits_asc(&256u16, bytes.iter().map(|b| (*b).into())).unwrap()
}
pub(crate) fn natural_to_bytes(value: &Natural) -> Vec<u8> {
  let mut res = value
    .to_digits_asc(&256u16)
    .into_iter()
    .map(|byte| byte.try_into().unwrap())
    .collect::<Vec<_>>();
  // Ensure this is a canonical encoding
  while res.last() == Some(&0) {
    res.remove(0);
  }
  res
}

fn euclid(a: &Integer, b: &Integer) -> (Integer, Integer) {
  let mut q = a / b;
  let mut r = a % b;
  if r.sign() == Ordering::Less {
    q -= Integer::ONE;
    r += b;
  }
  debug_assert_eq!((&q * b) + &r, *a);
  (q, r)
}

fn parteucl(a: Integer, b: Integer, L: &Integer) -> (Integer, Integer, Integer, Integer, Integer) {
  let mut v = Integer::ZERO;
  let mut d = a;
  let mut v2 = Integer::ONE;
  let mut v3 = b;
  let mut z = Integer::ZERO;
  while v3.unsigned_abs_ref() > L {
    let (q, t3) = euclid(&d, &v3);
    debug_assert_eq!(&(&q * &v3) + &t3, d);
    let t2 = &v - (&q * &v2);
    v = v2;
    d = v3;
    v2 = t2;
    v3 = t3;
    z += Integer::ONE;
  }
  if z.odd() {
    v2 = -v2;
    v3 = -v3;
  }
  (v, d, v2, v3, z)
}

/// An element of a class group, implemented with the variable-time Malachite.
///
/// This is a pure-Rust implementation and does not have a dependency on libraries in other
/// languages.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MalachiteElement {
  a: Integer,
  b: Integer,
  c: Integer,
  L: Integer,
}

impl MalachiteElement {
  // Algorithm 5.4.2 of A Course in Computational Algebraic Number Theory
  pub(crate) fn reduce(mut a: Integer, mut b: Integer, mut c: Integer, L: Integer) -> Self {
    // Step 2
    let normalize = |a: &mut Integer, b: &mut Integer, c: &mut Integer| {
      let two_a = a.clone() << 1;
      let (mut q, mut r) = euclid(b, &two_a);
      if r > *a {
        r -= two_a;
        q += Integer::ONE;
      }
      *c -= ((&*b + &r) * q) >> 1;
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
    if (a == c) && (b.sign() == Ordering::Less) {
      b = -b;
    }

    // Definition 5.3.2 of A Course in Computational Algebraic Number Theory
    // This is notable as it bounds a, c to being postive. Only b may be negative
    debug_assert!(b.clone().abs() <= a.clone());
    debug_assert!(a.clone() <= c.clone());
    debug_assert!(if (b.clone().abs() == a.clone()) || (a.clone() == c.clone()) {
      b.sign() != Ordering::Less
    } else {
      true
    });
    Self { a, b, c, L }
  }
}

impl crate::Element for MalachiteElement {
  fn is_identity(&self) -> subtle::Choice {
    u8::from((self.a == Natural::ONE) && (self.b == Natural::ONE)).into()
  }

  // Algorithm 5.4.8 of A Course in Computational Algebraic Number Theory
  fn double(&self) -> Self {
    let L = &self.L;

    let (d1, u, v) = self.b.clone().extended_gcd(&self.a);
    let d1: Integer = d1.into();
    debug_assert_eq!((&u * &self.b) + (&v * &self.a), d1);
    let A = &self.a / &d1;
    let B = &self.b / &d1;
    let mut C = -((&self.c * &u) % &A);
    let C1 = &A - &C;
    if C1 < C {
      C = -C1;
    }

    let (mut v, d, mut v2, v3, z) = parteucl(A.clone(), C, L);
    if z == Natural::ZERO {
      let g = ((&B * &v3) + &self.c) / &d;
      let a2 = &d * &d;
      let c2 = &v3 * &v3;
      let b2_part = &d + &v3;
      let b2 = &self.b + (&b2_part * &b2_part) - &a2 - &c2;
      let c2 = &c2 + (&g * &d1);
      return Self::reduce(a2, b2, c2, self.L.clone());
    }

    let e = ((&self.c * &v) + (&B * &d)) / &A;
    let g = ((&e * &v2) - &B) / &v;
    let mut b2 = (&e * &v2) + (&v * &g);
    if d1 > Integer::ONE {
      b2 = &d1 * &b2;
      v = &d1 * &v;
      v2 = &d1 * &v2;
    }
    let a2 = &d * &d;
    let c2 = &v3 * &v3;
    let b2_part = &d + &v3;
    let b2 = &b2 + (&b2_part * &b2_part) - &a2 - &c2;
    let a2 = &a2 + (&e * &v);
    let c2 = &c2 + (&g * &v2);
    Self::reduce(a2, b2, c2, self.L.clone())
  }

  // Algorithm 5.4.9 of A Course in Computational Algebraic Number Theory
  fn add(&self, other: &Self) -> MalachiteElement {
    if self.is_identity().into() {
      return other.clone();
    }
    if other.is_identity().into() {
      return self.clone();
    }

    let L = &self.L;

    let (f1, f2) = if self.a < other.a { (other, self) } else { (self, other) };
    let mut s = (&f1.b + &f2.b) >> 1u8;
    let n = &f2.b - &s;

    let (d, u, v) = f2.a.clone().extended_gcd(&f1.a);
    let mut d: Integer = d.into();
    debug_assert_eq!((&u * &f2.a) + (&v * &f1.a), d);

    let mut a1 = f1.a.clone();
    let mut a2 = f2.a.clone();

    let (A, d1) = if d == Natural::ONE {
      let A = -u * &n;
      let d1 = d;
      (A, d1)
    } else if (&s % &d) == Natural::ZERO {
      let A = -u * &n;
      let d1 = d;
      a1 /= &d1;
      a2 /= &d1;
      s /= &d1;
      (A, d1)
    } else {
      let (d1, u1, _) = s.clone().extended_gcd(&d);
      let d1: Integer = d1.into();
      if d1 > Integer::ONE {
        a1 /= &d1;
        a2 /= &d1;
        s /= &d1;
        d /= &d1;
      }

      let l = (&u * (&f1.c % &d)) + (v * (&f2.c % &d));
      let l = (&u1 * l) % &d;
      let l = &d - l;
      let A = (&l * (&a1 / &d)) - (u * (&n / &d));
      (A, d1)
    };

    let mut A = A % &a1;
    let A1 = &a1 - &A;
    if A1 < A {
      A = -A1;
    }

    let (mut v, d, mut v2, v3, z) = parteucl(a1.clone(), A, L);

    if z == Natural::ZERO {
      let Q1 = &a2 * &v3;
      let Q2 = &Q1 + &n;
      let f = &Q2 / &d;
      let g = ((&v3 * &s) + &f2.c) / &d;
      let a3 = &d * &a2;
      let c3 = (&v3 * &f) + (&g * &d1);
      let b3 = (Q1 << 1) + &f2.b;
      return Self::reduce(a3, b3, c3, self.L.clone());
    }

    let b = ((&a2 * &d) + (&n * &v)) / &a1;
    let Q1 = &b * &v3;
    let Q2 = &Q1 + &n;
    let f = &Q2 / &d;
    let e = ((&s * &d) + (&f2.c * &v)) / &a1;
    let Q3 = &e * &v2;
    let Q4 = &Q3 - &s;
    let g = &Q4 / &v;
    if d1 > Integer::ONE {
      v2 = &d1 * &v2;
      v = &d1 * &v;
    }

    let a3 = (&d * &b) + (&e * &v);
    let c3 = (&v3 * &f) + (&g * &v2);
    let b3 = (&Q1 + &Q2) + (&d1 * (&Q3 + &Q4));
    Self::reduce(a3, b3, c3, self.L.clone())
  }

  fn sub(&self, other: MalachiteElement) -> MalachiteElement {
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
    let a = natural_to_bytes(self.a.unsigned_abs_ref());
    let b = (
      u8::from(self.b.sign() != Ordering::Less).into(),
      natural_to_bytes(self.b.unsigned_abs_ref()),
    );
    let c = natural_to_bytes(self.c.unsigned_abs_ref());

    let discriminant = ((self.a.clone() * self.c.clone()) << 2u32) - self.b.clone().square();
    let discriminant = natural_to_bytes(discriminant.unsigned_abs_ref());

    (a, b, c, discriminant)
  }

  unsafe fn from_coefficients(
    a: impl AsRef<[u8]>,
    (b_positive, b_abs): (crypto_bigint::Choice, impl AsRef<[u8]>),
    c: impl AsRef<[u8]>,
    discriminant_abs: impl AsRef<[u8]>,
  ) -> Self {
    let to_malachite = |value: &[u8]| Integer::from(natural_from_bytes(value));

    let a = to_malachite(a.as_ref());

    let mut b = to_malachite(b_abs.as_ref());
    if !bool::from(b_positive) {
      b = -b;
    }

    let c = to_malachite(c.as_ref());

    // b^2 - 4ac = delta
    let delta: Integer = Integer::from(natural_from_bytes(discriminant_abs.as_ref()));
    let tess_root = delta.unsigned_abs().ceiling_root(4);

    Self { a, b, c, L: Integer::from(tess_root) }
  }
}

impl Neg for MalachiteElement {
  type Output = Self;
  fn neg(self) -> Self {
    Self::reduce(self.a, -self.b, self.c, self.L)
  }
}

impl crate::ElementExt for MalachiteElement {}
