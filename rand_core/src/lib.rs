//! A shim from `rand_core 0.6` to `rand_core 0.10`.

#![cfg_attr(not(feature = "std"), no_std)]

pub use rand_core_upstream::{Rng as RngCore, CryptoRng as CryptoRngCore, CryptoRng};

/// An infallible error type.
#[derive(Debug)]
pub enum Error {}
impl core::fmt::Display for Error {
  fn fmt(&self, _fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    Ok(())
  }
}
impl core::error::Error for Error {}
