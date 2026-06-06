#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(non_snake_case)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod element;
pub use element::{Coefficients, Element};

mod table;
pub use table::{Table, ElementExt};

mod malachite;
pub use malachite::MalachiteElement;

mod crypto_bigint;
pub use crypto_bigint::{Error, CryptoBigintElement};

mod primes;

mod class_group;
pub use class_group::ClassGroup;

mod discriminant;
pub use discriminant::{
  Discriminant, NegativeDiscriminant, OddDiscriminant, FundamentalDiscriminant, Cl15Error, Cl15k,
  Cl15p,
};
