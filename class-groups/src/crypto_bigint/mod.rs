/// A signed integer type.
///
/// The `Choice` represents if the number is positive. The other term represents the absolute
/// value of the number. When the number is zero, whether or not the number is considered positive
/// is undefined.
pub(super) type I<U> = (crypto_bigint::Choice, U);

pub(crate) mod c;
use c::c;

pub(crate) mod reduction;
pub(crate) use reduction::{partial_reduce, reduce};

mod composition;
pub(super) use composition::{add, double};

mod element;
pub use element::CryptoBigintElement;

mod uint;
#[cfg(feature = "alloc")]
mod boxed_uint;

mod encoding;
#[cfg(feature = "std")]
pub(crate) use encoding::{
  encode_compressed_binary_quadratic_form, decode_compressed_binary_quadratic_form,
};
pub use encoding::Error;

mod sqrt;
#[cfg_attr(not(feature = "alloc"), expect(unused_imports))]
pub(crate) use sqrt::{legendre_symbol, sqrt_mod_p_vartime};
