//! Uncompressed encoding of binary quadratic forms
//!
//! This implements uncompressed encoding of primitive reduced positive definite binary quadratic
//! forms of negative discriminants (even or odd) in a constant
//! $2 * \lceil \floor log_2(-discriminant) / 2 \rfloor / 8 \rceil$ bytes.
//!
//! This SHOULD NOT be used unless there's an explicit use-case for it (such as when strong bounds
//! on runtime complexity or constant-time encoding is needed).
//!
//! `^` is used to represent the binary XOR operation. `//` is used to represent floor division.
//!
//! `floor_log_2(x)` is assumed to yield $\lfloor log_2(x) \rfloor$ for a positive integer `x`.
//! Note that a number requires $\lfloor log_2(x) \rfloor + 1$ bits to be represented, not
//! $\lceil log_2(x) \rceil$.
//!
//! ```py
//! # Note `discriminant` is a _signed_ big integer, bound to be negative
//! fn encode_uncompressed_binary_quadratic_form(a, b_positive, b_abs, discriminant) {
//!   bits_per_element = floor_log_2(-discriminant) / 2
//!   bytes_per_element = (bits_per_element + 7) / 8
//!
//!   result = a.to_le_bytes()
//!   while result.len() < bytes_per_element {
//!     result.push(0)
//!   }
//!
//!   result.extend((b_abs ^ (!b_positive)).to_le_bytes())
//!   while result.len() < (2 * bytes_per_element) {
//!     result.push(0)
//!   }
//!
//!   return result
//! }
//!
//! # Note `discriminant` is a _signed_ big integer, bound to be negative
//! fn decode_uncompressed_binary_quadratic_form(bytestream, discriminant) {
//!   bits_per_element = (floor_log_2(-discriminant) // 2) + 1
//!   bytes_per_element = (bits_per_element + 7) / 8
//!
//!   a = []
//!   while a.len() < bytes_per_element {
//!     a.push(bytestream.next_byte())
//!   }
//!   a = BigInt::from_le_bytes(a)
//!
//!   b_abs = []
//!   while b_abs.len() < bytes_per_element {
//!     b_abs.push(bytestream.next_byte())
//!   }
//!   b_abs = BigInt::from_le_bytes(b_abs)
//!
//!   b_positive = (b_abs % 2) == (discriminant % 2)
//!   if !b_positive {
//!     b_abs = b_abs ^ 1
//!   }
//!
//!   return validate_binary_quadratic_form(a, b_positive, b_abs, discriminant)
//! }
//! ```
//!
//! $\lfloor log_2(-discriminant) / 2 \rfloor + 1$ is used as an approximation for the length of
//! the square root of the discriminant. Per Lemma 5.3.4 of
//! A Course in Computational Number Theory by Henri Cohen, a reduced `a` coefficient is less than
//! or equal to `sqrt(|D| / 3)`. This means our approximation is sufficient for any reduced `a`
//! coefficient.
//!
//! The absolute value of a reduced `b` coefficient will also be less than or equal to the `a`
//! coefficient, so it will fit within the bound. As for encoding its sign, we take advantage of
//! how $b \cong discriminant \mod 2$ to encode the sign bit in place of the (known-value)
//! least-significant bit to avoid requiring any additional bytes.
//!
//! These methods are described in a way which allocates, with lists to encode into and to store
//! bytes which are decoded from. As the amount of bytes in the encoding is constant to the
//! discriminant, a non-allocating implementation is actually quite immediate. The descriptions
//! above are only as-is for simplicity, not for explicit intent these be implemented with
//! allocations.
//!
//! We specifically align the uncompressed encoding exactly to byte boundaries, and do not remove
//! any zero bytes, to ensure simplicity and the possibility of constant-time encoding.
//! Constant-time encoding MAY be necessary for protocols which involve secret forms, where
//! non-interactive multiplication (as seen in
//! [Non-Interactive Distributed Point Functions](https://eprint.iacr.org/2025/095) by
//! Elette Boyle, Lalita Devadas, Sacha Servan-Schreiber) is an example of a scheme with secret
//! forms (but does not necessarily encode them). For those who want a more compact encoding,
//! again, the compressed encoding SHOULD be used unless there's explicit reason to use this
//! uncompressed encoding.
