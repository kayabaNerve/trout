#![cfg_attr(not(feature = "std"), no_std)]

pub use rand_core_upstream::{Rng as RngCore, CryptoRng as CryptoRngCore, CryptoRng};
#[derive(Debug)]
pub enum Error {}
impl core::fmt::Display for Error {
  fn fmt(&self, _fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    Ok(())
  }
}
impl core::error::Error for Error {}
