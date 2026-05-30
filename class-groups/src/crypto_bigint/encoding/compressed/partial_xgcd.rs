//! A partial extended Euclidean algorithm
//!
//! This is derived from `PartialXGCD`, Algorithm 1 of
//! [Trustless unknown-order groups](https://eprint.iacr.org/2020/196)
//! by Samuel Dobson, Steven Galbraith, and Benjamin Smith. It's been adapted to more closely
//! resemble the binary extended Euclidean algorithm for performance reasons and to simplify
//! implementation.
//!
//! Implementations of this function MUST return the singular canonical value consistent with the
//! specification. Other partial extended Euclidean algorithms MUST NOT be used UNLESS they yield
//! identical results. It's for this reason that the described algorithm is the efficient binary
//! adaptation, rather than the existing one which was already proven.
//!
//! The pseudocode denotes what we would discuss as `s'` as `s_apo`, instead of the more
//! traditional `s_prime`. This is to avoid confusion on if this variable is notably considered
//! (co)prime.
//!
//! We assume the existence of a `floor_sqrt` function, which for `floor_sqrt(x)` where `x` is a
//! positive unsigned integer, yields `y` such that $y^2 \le x, x < (y + 1)^2$. We also assume the
//! existence of a `max` function which for `max(x, y)` yields `x` if $x \ge y$ else `y`.
//!
//! `**` is used to notate exponentation.
//!
//! ```py
//! fn t(a, b) {
//!   ceil_sqrt_a = floor_sqrt(a)
//!   if (ceil_sqrt_a * ceil_sqrt_a) != a {
//!     ceil_sqrt_a += 1
//!   }
//!
//!   (s, s_apo, t, t_apo) = (b, a, 1, 0)
//!   while s >= ceil_sqrt_a {
//!     log_2_q = max(floor(log_2(s_apo)) - floor(log_2(s)) - 1, 0)
//!     q = 2**log_2_q
//!
//!     # Note `t_apo` is a _signed_ integer operation, though we do bound `s_apo >= 0`
//!     (s_apo, t_apo, u_apo) = (s_apo - q * s, t_apo - q * t)
//!     if s_apo < s {
//!       (s, s_apo, t, t_apo, u, u_apo) = (s_apo, s, t_apo, t)
//!     }
//!   }
//!
//!   # Convert `t` from signed to unsigned (with sign bit)
//!   t_positive = t >= 0
//!   if t < 0 {
//!     t = -t
//!   }
//!
//!   (t_positive, t_abs)
//! }
//! ```
//!
//! For input $0 < a$, $0 \le b \le a$, the function `t` yields `(t_positive, t_abs)` representing
//! a number `t` satisfying $s \cong t * b \mod a$, where $0 \le s < sqrt(a)$ and
//! $0 < t \le sqrt(a)$. Its loop terminates within
//! $2 * \lfloor log_2(a) \rfloor + 1 + \lfloor log_2(b) \rfloor + 1$ iterations.
//!
//! $s \le s'$ is an invariant of our loop, as holds true at initialization ($s, s' = b, a$ where
//! $b \le a$) and at the end of each iteration of our loop (as if $s' < s$, the two are swapped).
//!
//! $q s \le s'$ holds from the choice of
//! $q = 2^{max(\lfloor log_2(s_apo) \rfloor - \lfloor log_2(s) \rfloor - 1, 0)}$. When $s'$ has
//! bit-length exceeding $s$, $q s$ has bit-length less than $s'$. When $s'$ has bit-length equal
//! to $s$, $q = 1$ and $q s = s$ where $s \le s'$ is an invariant of our loop.
//!
//! `s` is initialized to `b` and only updated when swapped with `s'`, which only happens when
//! `s' < s`. This allows us to bound `s` as strictly decreasing and never of size exceeding `b`.
//!
//! `s'` is initialized to `a` and with each iteration, updated to `s' = s' - q s` where
//! $q s \le s'$ has already been proven to hold. This lets us bound $0 \le s' \le a$ (and
//! therefore $0 \le s$).
//!
//! `s'` is reduced by at least one bit every two iterations, effecting our termination bound of
//! $2 * \lfloor log_2(a) \rfloor + 1 + \lfloor log_2(b) \rfloor + 1$. This is as $2 q s$ has
//! bit-length equal to or greater than $s'$ and the difference of two numbers with equal
//! bit-length has itself a smaller bit-length. This does have a factor of `2` compared to the
//! traditional bound on the termination of the binary extended Euclidean algorithm, which is
//! required to ensure we iterate over the `s, t` pair for which our bounds on the output are
//! satisfied. A tighter bound is still possible as we terminate when $s < sqrt(a)$ yet the
//! described bound would be for if we terminated when $s = 1$ (assuming $a, b$ coprime). As this
//! current bound on termination is sufficient, we do not put in the work on further analysis here
//! as it's simply unnecessary.
//!
//! The function only terminates once $s < sqrt(a)$, so therefore our bounds on the result that
//! $0 \le s < sqrt(a)$ have been proven.
//!
//! To satisfy $0 < t$, we prove $t = 0$ never occurs. $t$ is initialized to $1$ and will be one if
//! the loop doesn't iterate. If the loop does iterate, on its first iteration, we have
//! $t' = t' - q t$ where $t' = 0$ and therefore $t' = -q t$. As $0 < q$, this first iteration of
//! assigns $t'$ to have the opposite sign of $t$. This is preserved throughout further iterations
//! as the swap of $t, t'$ does not change how they have opposing signs and $t' = t' - q t$ causes
//! $t'$ to maintain its existing sign (as the difference of numbers with opposite signs is the sum
//! of their absolute value with the sign of the number subtracted from). Having established that
//! if the loop iterates, $t, t'$ have distinct signs, we note it's impossible for $t'$ to be set
//! to $0$ (except when initialized) as that would require $t' = t' - q t = (q t) - q t = 0$ (when
//! we have proven $t \ne t'$). In turn, this makes it impossible for $t$ to be set to $0$, as $t$
//! is only updated when swapped with $t'$.
//!
//! We continue to specifically prove the invariant $s' |t| \le a$ by proving the invariant
//! $s' |t| + s |t'| = a$. This invariant, via this second invariant, was proven as part of
//! Mathematics of Public Key Cryptography by Steven Galbraith, Lemma 2.3.3, but we provide the
//! proof here for completeness and as it doesn't immediately apply (due to explicitly being for
//! their described Euclidean algorithm which does not match our described Euclidean algorithm). At
//! initialization, we have `(s, s', t, t') = (b, a, 1, 0)`, which upholds the invariant. It's
//! clear the swap preserves the invariant, leaving us to prove the updates
//! (`s' = s' - q s, t' = t' - q s`) do. By expansion,
//! $s' |t| + s |t'| = a = (s' - q s) |t| + s |(t' - q t)|$ requires $(-q s) |t| + s |q t| = 0$,
//! which is clear.
//!
//! As $|s' t| \le a$, we can therefore bound $t \le sqrt(a)$ by proving $s' \ge sqrt(a)$. The loop
//! terminates when $s < sqrt(a)$. As $s'$ _was_ the $s$ value prior to this final swap, if the
//! loop ever iterated, but the loop did not terminate, $s'$ must have been greater than or equal
//! to $sqrt(a)$. If the loop never iterated, then we have $s' = a$ (as initialized) where
//! $a \ge sqrt(a)$ as $0 < a$.
//!
//! $s \cong t * b \mod a$ is a result of two invariants:
//! - $s \cong b t \mod a$
//! - $s' \cong b t' \mod a$
//!
//! At initialization, we have $s, s', t, t' = b, a, 1, 0$, for which these are upheld. During the
//! loop, we update:
//! - `s' = s' - q s`
//! - `t' = t' - q t`
//!
//! For the relevant invariant which requires $(s' - q s) \cong b (t' - qt ) \mod a$, we may expand
//! this as $b t' - q b t \cong b (t' - q t) \mod a$, which is clearly correct. The only other
//! updates during the loop are the potential simultaneously swap of $s', t'$ with $s, t$, also
//! upholding the invariants.

use crypto_bigint::{Choice, NonZero, Resize, ConcatenatingSquare, BoxedUint};

/// The implementation of the `t` function as described in the specification.
///
/// This function runs in time variable to the input. While a constant-time variant is feasible, as
/// the binary GCD is itself feasible to implement in constant-time and we have a bound on
/// termination, there's not currently value to such an implementation when compression as a whole
/// is currently posited in variable-time.
pub(super) fn t(a: NonZero<BoxedUint>, b: BoxedUint) -> (Choice, NonZero<BoxedUint>) {
  let ceil_sqrt_a = {
    let floor_sqrt_a = a.as_ref().floor_sqrt_vartime();
    if floor_sqrt_a.concatenating_square() == a.as_ref() {
      floor_sqrt_a
    } else {
      floor_sqrt_a + BoxedUint::one()
    }
  };

  let precision = a.bits_precision();
  let (mut s, mut s_apo, mut t, mut t_apo) = (
    b.clone().resize(precision),
    a.as_ref().clone(),
    (Choice::TRUE, BoxedUint::one_with_precision(precision)),
    (Choice::TRUE, BoxedUint::zero_with_precision(precision)),
  );

  let mut i = 0;
  while s >= ceil_sqrt_a {
    #[cfg(debug_assertions)]
    {
      use crypto_bigint::CtSelect;
      let t = <_>::ct_select(&t.1.neg_mod(&a), &t.1, t.0);
      let t_apo = <_>::ct_select(&t_apo.1.neg_mod(&a), &t_apo.1, t_apo.0);
      debug_assert_eq!(b.mul_mod(&t, &a), s.rem(&a));
      debug_assert_eq!(b.mul_mod(&t_apo, &a), s_apo.rem(&a));
    }

    let log_2_q = (s_apo.bits_vartime() - s.bits_vartime()).saturating_sub(1);

    {
      let qs = s.clone() << log_2_q;
      // $q |s| < s'$
      s_apo = if s_apo < qs { qs - s_apo } else { s_apo - qs };
    }

    {
      let qt = t.1.clone() << log_2_q;
      if i == 0 {
        // `t' = t' - qt`, optimized with the knowledge `t' = 0`
        t_apo = (!t_apo.0, qt);
      } else {
        // `t' = t' - q t`, optimized with the knowledge $sgn(t') \ne sgn(t)$
        t_apo = (t_apo.0, t_apo.1 + qt);
      }
    }

    if s_apo < s {
      (s, s_apo, t, t_apo) = (s_apo, s, t_apo, t);
    }

    i += 1;
  }

  let (t_positive, t_abs) = t;
  (t_positive, NonZero::new(t_abs).expect("`t` proven to be non-zero"))
}

#[test]
fn test() {
  use rand::Rng;
  use crypto_bigint::{CtSelect, RandomBits, RandomMod};

  let mut rng = rand::rand_core::UnwrapErr(rand::rngs::SysRng);

  let non_zero_a = |rng: &mut _| {
    // Sample a non-zero `a`
    let mut a;
    while {
      const BITS: u32 = 512;
      a = NonZero::new(BoxedUint::random_bits(&mut *rng, BITS));
      bool::from(a.is_none())
    } {}
    a.unwrap()
  };

  // Test `(0, 1)`
  {
    let a = NonZero::new(BoxedUint::one()).unwrap();
    let b = BoxedUint::zero();
    let (t_positive, t_abs) = t(a, b);
    assert!(bool::from(t_positive));
    assert_eq!(t_abs, NonZero::new(BoxedUint::one()).unwrap());
  }

  // Test `(1, 1)`
  {
    let a = NonZero::new(BoxedUint::one()).unwrap();
    let b = BoxedUint::one();
    let (t_positive, t_abs) = t(a, b);
    assert!(bool::from(!t_positive));
    assert_eq!(t_abs, NonZero::new(BoxedUint::one()).unwrap());
  }

  // Test `(0, rand())`
  {
    let a = non_zero_a(&mut rng);
    let b = BoxedUint::zero();
    let (t_positive, t_abs) = t(a, b);
    assert!(bool::from(t_positive));
    assert_eq!(t_abs, NonZero::new(BoxedUint::one()).unwrap());
  }

  for _ in 0 .. 1024 {
    // Sample a non-zero `a`
    let a = non_zero_a(&mut rng);

    // Sample `0 <= b <= a`
    let mut b = {
      let a_plus_one =
        NonZero::new(a.as_ref().clone().concatenating_add(BoxedUint::one())).unwrap();
      BoxedUint::random_mod_vartime(&mut rng, &a_plus_one)
    };

    // Ensure `b == a` a fourth of the time
    #[expect(clippy::manual_is_multiple_of)]
    if (rng.next_u64() % 4) == 0 {
      b = a.as_ref().clone();
    }

    let (t_positive, t_abs) = t(a.clone(), b.clone());
    let t_abs = t_abs.get();

    // $t * b \cong s \mod a$
    let s_abs = t_abs.mul_mod(&b, &a);
    let s = <_>::ct_select(&s_abs.neg_mod(&a), &s_abs, t_positive);

    let floor_sqrt_a = a.floor_sqrt_vartime();
    assert!(s < floor_sqrt_a);
    assert!(t_abs <= floor_sqrt_a);
  }
}
