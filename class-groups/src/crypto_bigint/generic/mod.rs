/// A signed integer type.
///
/// The `Choice` represents if the number is positive. The other term represents the absolute
/// value of the number. When the number is zero, whether or not the number is considered positive
/// is undefined.
pub(super) type I<U> = (crypto_bigint::Choice, U);

mod c;
use c::c;

mod reduction;
pub(super) use reduction::{partial_reduce, reduce};

mod composition;
pub(super) use composition::{add, double};

mod element;
pub use element::CryptoBigintElement;

mod uint;
mod boxed_uint;

/// A type supporting discriminants of up to `2560` bits.
#[deprecated]
pub type CryptoBigintStackElement =
  CryptoBigintElement<crypto_bigint::Uint<{ crypto_bigint::nlimbs((2560u32 + 2).div_ceil(2)) }>>;
/// A type supporting unbounded discriminants but requiring allocations on the heap.
#[deprecated]
pub type CryptoBigintHeapElement = CryptoBigintElement<crypto_bigint::BoxedUint>;
