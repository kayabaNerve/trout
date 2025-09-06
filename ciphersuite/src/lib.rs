#![cfg_attr(not(feature = "std"), no_std)]

use std_shims::io;

use zeroize::Zeroize;
pub use ciphersuite_upstream::group;
use group::{*, ff::*, prime::PrimeGroup};

pub trait Ciphersuite: 'static + Send + Sync {
  type F: PrimeField + PrimeFieldBits + Zeroize;
  type G: Group<Scalar = Self::F> + GroupOps + PrimeGroup + Zeroize;
  #[cfg(feature = "alloc")]
  #[allow(non_snake_case)]
  fn read_F<R: io::Read>(reader: &mut R) -> io::Result<Self::F>;
  #[cfg(feature = "alloc")]
  #[allow(non_snake_case)]
  fn read_G<R: io::Read>(reader: &mut R) -> io::Result<Self::G>;
}
impl<C: ciphersuite_upstream::GroupIo> Ciphersuite for C {
  type F = <C as ciphersuite_upstream::WrappedGroup>::F;
  type G = <C as ciphersuite_upstream::WrappedGroup>::G;
  #[cfg(feature = "alloc")]
  fn read_F<R: io::Read>(reader: &mut R) -> io::Result<Self::F> {
    <C as ciphersuite_upstream::GroupIo>::read_F(reader)
  }
  #[cfg(feature = "alloc")]
  fn read_G<R: io::Read>(reader: &mut R) -> io::Result<Self::G> {
    <C as ciphersuite_upstream::GroupIo>::read_G(reader)
  }
}
