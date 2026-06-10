#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]
#![no_std]
#![deny(missing_docs)]
#![allow(non_snake_case)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

mod element;
pub use element::{Coefficients, Element};

mod mul;
pub use mul::Table;

mod crypto_bigint;
pub use crypto_bigint::{Error, CryptoBigintElement};

mod primes;

mod discriminant;
pub use discriminant::{
  Discriminant, NegativeDiscriminant, OddDiscriminant, FundamentalDiscriminant, Cl15Error,
  Cl15kParameters, QApostraphe, Cl15k, Cl15p,
};
