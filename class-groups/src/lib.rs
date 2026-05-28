#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(non_snake_case)]

pub(crate) mod compression;

mod element;
pub use element::*;

mod malachite;
pub use malachite::MalachiteElement;

mod crypto_bigint;
pub use crypto_bigint::CryptoBigintElement;
#[expect(deprecated)]
pub use crypto_bigint::{CryptoBigintStackElement, CryptoBigintHeapElement};

#[cfg(feature = "gmp")]
mod gmp;
#[cfg(feature = "gmp")]
pub use gmp::GmpElement;

mod primes;

mod class_group;
pub use class_group::ClassGroup;
