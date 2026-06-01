#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(non_snake_case)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod element;
pub use element::*;

mod table;
pub use table::*;

mod malachite;
pub use malachite::MalachiteElement;

mod crypto_bigint;
pub use crypto_bigint::{Error, CryptoBigintElement};
#[expect(deprecated)]
pub use crypto_bigint::{CryptoBigintStackElement, CryptoBigintHeapElement};

#[cfg(feature = "gmp")]
mod gmp;
#[cfg(feature = "gmp")]
pub use gmp::GmpElement;

mod primes;

mod class_group;
pub use class_group::ClassGroup;
