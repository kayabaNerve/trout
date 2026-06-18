use crypto_bigint::{Choice, Limb};

/// The required view over a collection of limbs to calculate the `c` coefficient.
///
/// Implementations MUST implement all functions in time constant to the value of the inputs,
/// except for the amount of limbs, unless otherwise stated. Implementations MUST NOT panic for any
/// input which the caller MAY pass.
pub(super) trait Limbs: Clone + AsRef<[Limb]> + AsMut<[Limb]> {
  /// Square the value, returning the `(lo, hi)` terms.
  ///
  /// Implementations MUST ensure each part of the result has an amount of limbs equal to how many
  /// limbs the input has.
  fn widening_square(&self) -> (Self, Self);

  /// Divide `num` by `denom`, returning the low bits.
  ///
  /// Callers MUST ensure both parts of the numerator have an equivalent amount of limbs. Callers
  /// MUST ensure `num` is divisible by `denom` and `denom` is NOT `0`.
  ///
  /// Implementations MUST ensure the result has an amount of limbs equal to how many limbs each
  /// part of the input has.
  fn wrapping_div_exact(num: (Self, Self), denom: &Self) -> Self;

  /// Calculate the remainder of `num % denom`.
  ///
  /// Callers MUST NOT specify `denom = 0`.
  fn rem(num: Self, denom: &Self) -> Self;
}

/// Calculate `c` such that `b^2 - 4ac = delta`.
///
/// The following bounds are present:
/// - `delta < 0`
/// - There is an integer solution for `c` in `b^2 - 4 a c = delta`.
/// - `<_ as AsRef<[Limb]>>::as_ref(a).len() <= <_ as AsRef<[Limb]>>::as_ref(&b.1).len()`
/// - `<_ as AsRef<[Limb]>>::as_ref(negative_discriminant_abs).len() <=
///      2 * <_ as AsRef<[Limb]>>::as_ref(&b.1).len()`
/// - `b < 2a`
/// - $floor(log_2(|delta|)) + 1 < <_ as AsRef<[Limb]>>::as_ref(a).len() * Limb::BITS$
/// - $floor(log_2(|a|)) + 1 < <_ as AsRef<[Limb]>>::as_ref(a).len() * Limb::BITS$
///
/// `delta` is specified via its absolute value in `negative_discriminant_abs`.
pub(crate) fn c<L: Limbs>(a: &L, b: &(Choice, L), negative_discriminant_abs: &L) -> L {
  let (mut b_lo, mut b_hi) = b.1.widening_square();

  /*
    `b^2 - 4ac = -|delta|`
    `b^2 + |delta| = 4ac`

    We simultaneously add `|delta|` and divide by four to obtain `ac`. Because `|delta|` is of size
    at most the size of `b^2`, their sum is at most one bit bigger, while the simultaneous division
    by `4` ensures the result is two bits smaller. Therefore, `(b^2 + |delta|) / 4` fits in the
    container `b^2` fits in.
  */
  let mut carry = Limb::ZERO;
  for i in 0 .. (b_lo.as_ref().len() + b_hi.as_ref().len()) {
    let b_limb = if let Some(i) = i.checked_sub(b_lo.as_ref().len()) {
      &mut b_hi.as_mut()[i]
    } else {
      &mut b_lo.as_mut()[i]
    };

    let new_limb;
    (new_limb, carry) =
      b_limb.carrying_add(*negative_discriminant_abs.as_ref().get(i).unwrap_or(&Limb::ZERO), carry);

    // The lowest two bits should be assigned to the prior limb, as their highest two bits
    let shift_down = new_limb << (Limb::BITS - 2);
    *b_limb = new_limb >> 2;

    if let Some(i) = i.checked_sub(1) {
      let b_limb = if let Some(i) = i.checked_sub(b_lo.as_ref().len()) {
        &mut b_hi.as_mut()[i]
      } else {
        &mut b_lo.as_mut()[i]
      };
      *b_limb |= shift_down;
    }
  }
  // The `carry` becomes the highest two bits of the highest limb in `b`
  *b_hi.as_mut().last_mut().unwrap() |= carry << (Limb::BITS - 2);
  let ac = (b_lo, b_hi);

  /*
    As `b^2` is positive yet `delta < 0`, `4ac` must be non-zero. Therefore, `a` must be non-zero
    if this is a valid form, making this division safe.

    We also know `c < |delta|`, and will fit in the same container as `b_lo`  does, due to
    requiring `b < 2a`. Substituting `b` for its bound `2a`, we have:
    `(2a)^2 + |delta| = 4ac`
    `(4a^2 + |delta|) / 4a = c`
    `a + |delta| = c`
    where the sum of `a + |delta|` is bound to fit in the container for `a`, which is of less than
    or equal capacity to the container for `b.1` (itself of equal capacity to `b_lo, b_hi`).
  */
  L::wrapping_div_exact(ac, a)
}
