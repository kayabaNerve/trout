use core::{marker::PhantomData, ops::Deref as _};
use std::io::{self, Read as _, Write as _};

use zeroize::Zeroizing;
use rand::CryptoRng;

use ::malachite::base::num::logic::traits::*;

use group::ff::{Field, PrimeField};
use class_groups::{ElementExt, Table, ClassGroup};

use crate::{UnsignedInteger, DigestReader, DigestWriter, Primes, Parameters};

/// The proofs for the second round.
///
/// These proofs need to prove
/// `A_i = alpha_i \cdot G + a_i \cdot H, B_i = beta_i \cdot G,
///  F = (b_i \cdot A) - (alpha_i \cdot B)` for
/// `A_i = Z_i, B_i = U_i, A = Z, B = U` and `A_i = K_i, B_i = U_i, A = K, B = U` in order to
/// achieve identifiable aborts. Proofs MAY not do anything if forgoing identifiable aborts in
/// favor of efficiency is preferred.
///
/// Given how both instantiations open `B_i, B`, a composition of the two proofs is
/// *strongly recommended*.
//
// The following doesn't define a `BatchVerifier` as we only verify these if we have an invalid
// signature. In that case, while a batch verifier could binary search for invalid elements, that
// still has a worst-case linear complexity to the amount of proofs which are invalid (since all
// invalid proofs are expected to be yielded).
pub trait RoundTwoProofs<CG: ElementExt, P: Parameters<CG>> {
  /// Prove the round two statements.
  ///
  /// The provided context hash MUST be binding to `G, Z, K, U, Z_i, K_i, U_i`. This allows the
  /// proofs to not transcript these.
  ///
  /// `neg_U` is `-U`.
  ///
  /// If an error is returned, the state of `proof` is undefined.
  fn prove<W: io::Write>(
    rng: &mut impl CryptoRng,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Z: &Table<CG>,
    K: &Table<CG>,
    neg_U: &Table<CG>,
    delta_i: &UnsignedInteger,
    x_i: &P::F,
    alpha_i: &UnsignedInteger,
    k_i: &P::F,
    beta_i: &UnsignedInteger,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()>;

  /// Verify someone's round two proofs.
  ///
  /// This context must be the exact same as the prover used, causing the same bounds on what has
  /// already been transcripted.
  ///
  /// `neg_U` is `-U`.
  ///
  /// If an error is returned, `proof` is left in an undefined state.
  fn verify<R: io::Read>(
    rng: &mut impl CryptoRng,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Z: &Table<CG>,
    K: &Table<CG>,
    neg_U: &Table<CG>,
    Z_i: CG,
    K_i: CG,
    U_i: CG,
    ZU_i: CG,
    KU_i: CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()>;
}

/// No identifiable aborts.
///
/// This forgoes the round two proofs, sacrificing identifiable aborts, in the name of efficiency.
pub struct NoIdentifiableAborts;
impl<CG: ElementExt, P: Parameters<CG>> RoundTwoProofs<CG, P> for NoIdentifiableAborts {
  fn prove<W: io::Write>(
    _rng: &mut impl CryptoRng,
    _class_group: &ClassGroup<CG>,
    _G: &Table<CG>,
    _Z: &Table<CG>,
    _K: &Table<CG>,
    _neg_U: &Table<CG>,
    _delta_i: &UnsignedInteger,
    _x_i: &P::F,
    _alpha_i: &UnsignedInteger,
    _k_i: &P::F,
    _beta_i: &UnsignedInteger,
    _transcript: &mut DigestWriter<W>,
  ) -> io::Result<()> {
    Ok(())
  }

  fn verify<R: io::Read>(
    _rng: &mut impl CryptoRng,
    _class_group: &ClassGroup<CG>,
    _G: &Table<CG>,
    _Z: &Table<CG>,
    _K: &Table<CG>,
    _neg_U: &Table<CG>,
    _Z_i: CG,
    _K_i: CG,
    _U_i: CG,
    _ZU_i: CG,
    _KU_i: CG,
    _transcript: &mut DigestReader<R>,
  ) -> io::Result<()> {
    Ok(())
  }
}

/// Proofs from Cui, Chan, Yuen, Kang, and Chu's Bandwidth-Efficient Zero-Knowledge Proofs for
/// Threshold ECDSA (2023).
pub struct Ccykc2023RoundTwo<Pr: Primes>(PhantomData<Pr>);
impl<CG: ElementExt, P: Parameters<CG>, Pr: Primes> RoundTwoProofs<CG, P>
  for Ccykc2023RoundTwo<Pr>
{
  fn prove<W: io::Write>(
    rng: &mut impl CryptoRng,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Z: &Table<CG>,
    K: &Table<CG>,
    neg_U: &Table<CG>,
    delta_i: &UnsignedInteger,
    x_i: &P::F,
    alpha_i: &UnsignedInteger,
    k_i: &P::F,
    beta_i: &UnsignedInteger,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()> {
    let B = crate::ccykc::B::<P::F, _>(class_group);

    let r_delta_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    let r_x_i = Zeroizing::new(P::F::random(&mut *rng));
    let r_alpha_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    let r_k_i = Zeroizing::new(P::F::random(&mut *rng));
    let r_beta_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));

    // Nonce commitments for each invocation
    CG::multiexp(
      class_group.identity_p(),
      &[
        (G, &Zeroizing::new(r_delta_i.to_be_bytes())),
        (class_group.f(), &Zeroizing::new(crate::be_bytes(r_x_i.deref()))),
      ],
    )
    .compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[
        (G, &Zeroizing::new(r_alpha_i.to_be_bytes())),
        (class_group.f(), &Zeroizing::new(crate::be_bytes(r_k_i.deref()))),
      ],
    )
    .compress(&mut *transcript)?;
    CG::mul(G, &Zeroizing::new(r_beta_i.to_be_bytes())).compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[
        (Z, &Zeroizing::new(r_beta_i.to_be_bytes())),
        (neg_U, &Zeroizing::new(r_delta_i.to_be_bytes())),
      ],
    )
    .compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[
        (K, &Zeroizing::new(r_beta_i.to_be_bytes())),
        (neg_U, &Zeroizing::new(r_alpha_i.to_be_bytes())),
      ],
    )
    .compress(&mut *transcript)?;

    // Sample the challenge
    let c = P::from_xof(transcript.0.finalize_xof());
    let c_uint = UnsignedInteger::from_be_slice(&crate::be_bytes(&c));
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());
    let modulus = crypto_bigint::NonZero::new(
      (&prime * &UnsignedInteger::from_be_slice(class_group.p().as_ref())).0,
    )
    .unwrap();

    let s_delta_i = Zeroizing::new(r_delta_i.deref() + &Zeroizing::new(&c_uint * delta_i));
    let s_x_i = (c * x_i) + r_x_i.deref();
    let s_alpha_i = Zeroizing::new(r_alpha_i.deref() + &Zeroizing::new(&c_uint * alpha_i));
    let s_k_i = (c * k_i) + r_k_i.deref();
    let s_beta_i = Zeroizing::new(r_beta_i.deref() + &Zeroizing::new(&c_uint * beta_i));

    let (d_delta_i, e_delta_i) = s_delta_i.div_rem(&modulus);
    let (d_alpha_i, e_alpha_i) = s_alpha_i.div_rem(&modulus);
    let (d_beta_i, e_beta_i) = s_beta_i.div_rem(&modulus);

    // The `D` for each invocation
    CG::mul(G, &d_delta_i).compress(&mut *transcript)?;
    CG::mul(G, &d_alpha_i).compress(&mut *transcript)?;
    CG::mul(G, &d_beta_i).compress(&mut *transcript)?;
    CG::multiexp(class_group.identity_p(), &[(Z, &d_beta_i), (neg_U, &d_delta_i)])
      .compress(&mut *transcript)?;
    CG::multiexp(class_group.identity_p(), &[(K, &d_beta_i), (neg_U, &d_alpha_i)])
      .compress(&mut *transcript)?;

    // Each `e`
    crate::ccykc::write_e(&mut *transcript, &modulus, e_delta_i)?;
    transcript.write_all(s_x_i.to_repr().as_ref())?;
    crate::ccykc::write_e(&mut *transcript, &modulus, e_alpha_i)?;
    transcript.write_all(s_k_i.to_repr().as_ref())?;
    crate::ccykc::write_e(&mut *transcript, &modulus, e_beta_i)
  }

  fn verify<R: io::Read>(
    rng: &mut impl CryptoRng,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Z: &Table<CG>,
    K: &Table<CG>,
    neg_U: &Table<CG>,
    Z_i: CG,
    K_i: CG,
    U_i: CG,
    ZU_i: CG,
    KU_i: CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()> {
    let R_Z_i = class_group.decompress_p(&mut *transcript)?;
    let R_K_i = class_group.decompress_p(&mut *transcript)?;
    let R_U_i = class_group.decompress_p(&mut *transcript)?;
    let R_ZU_i = class_group.decompress_p(&mut *transcript)?;
    let R_KU_i = class_group.decompress_p(&mut *transcript)?;

    let c = P::from_xof(transcript.0.finalize_xof());
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());
    let c = crate::ccykc::natural_from_bytes(&crate::be_bytes(&c));
    let prime = crate::ccykc::natural_from_bytes(&prime.to_be_bytes());
    let modulus = &prime * &crate::ccykc::natural_from_bytes(class_group.p().as_ref());

    let D_Z_i = class_group.decompress_p(&mut *transcript)?;
    let D_K_i = class_group.decompress_p(&mut *transcript)?;
    let D_U_i = class_group.decompress_p(&mut *transcript)?;
    let D_ZU_i = class_group.decompress_p(&mut *transcript)?;
    let D_KU_i = class_group.decompress_p(&mut *transcript)?;

    let e_delta_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;
    let mut s_x_i = <P::F as PrimeField>::Repr::default();
    transcript.read_exact(s_x_i.as_mut())?;
    let s_x_i = Option::<P::F>::from(P::F::from_repr(s_x_i))
      .ok_or_else(|| io::Error::other("invalid s_x_i"))?;
    let e_alpha_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;
    let mut s_k_i = <P::F as PrimeField>::Repr::default();
    transcript.read_exact(s_k_i.as_mut())?;
    let s_k_i = Option::<P::F>::from(P::F::from_repr(s_k_i))
      .ok_or_else(|| io::Error::other("invalid s_k_i"))?;
    let e_beta_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;

    let table = |scalar_bits: u64, point| {
      Table::new_for_scalar_bits(
        scalar_bits.try_into().unwrap(),
        class_group.identity_p().clone(),
        point,
      )
    };

    let D_Z_i = table(modulus.significant_bits(), D_Z_i);
    let D_K_i = table(modulus.significant_bits(), D_K_i);
    let D_U_i = table(modulus.significant_bits(), D_U_i);
    let D_ZU_i = table(modulus.significant_bits(), D_ZU_i);
    let D_KU_i = table(modulus.significant_bits(), D_KU_i);
    let R_Z_i = table(128, -R_Z_i);
    let R_K_i = table(128, -R_K_i);
    let R_U_i = table(128, -R_U_i);
    let R_ZU_i = table(128, -R_ZU_i);
    let R_KU_i = table(128, -R_KU_i);
    let Z_i = table(c.significant_bits(), -Z_i);
    let K_i = table(c.significant_bits(), -K_i);
    let U_i = table(c.significant_bits(), -U_i);
    let ZU_i = table(c.significant_bits(), -ZU_i);
    let KU_i = table(c.significant_bits(), -KU_i);

    let mut weight = || {
      let mut weight = [0; 16];
      rng.fill_bytes(&mut weight);
      crate::ccykc::natural_from_bytes(&weight)
    };
    let weight_Z = weight();
    let weight_K = weight();
    let weight_U_i = weight();
    let weight_ZU_i = weight();
    let weight_KU_i = weight();

    let D_Z_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_Z * &modulus));
    let mut G_scalar = &weight_Z * &e_delta_i;
    let mut H_scalar = &weight_Z * crate::ccykc::natural_from_bytes(&crate::be_bytes(&s_x_i));
    let Z_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_Z * &c));
    let R_Z_i_scalar = crate::ccykc::natural_to_bytes(&weight_Z);

    let D_K_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_K * &modulus));
    G_scalar += &weight_K * &e_alpha_i;
    H_scalar += &weight_K * crate::ccykc::natural_from_bytes(&crate::be_bytes(&s_k_i));
    let K_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_K * &c));
    let R_K_i_scalar = crate::ccykc::natural_to_bytes(&weight_K);

    let D_U_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_U_i * &modulus));
    G_scalar += &weight_U_i * &e_beta_i;
    let U_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_U_i * &c));
    let R_U_i_scalar = crate::ccykc::natural_to_bytes(&weight_U_i);

    let D_ZU_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_ZU_i * &modulus));
    let mut neg_U_scalar = &weight_ZU_i * &e_delta_i;
    let Z_scalar = crate::ccykc::natural_to_bytes(&(&weight_ZU_i * &e_beta_i));
    let ZU_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_ZU_i * &c));
    let R_ZU_i_scalar = crate::ccykc::natural_to_bytes(&weight_ZU_i);

    let D_KU_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_KU_i * &modulus));
    neg_U_scalar += &weight_KU_i * &e_alpha_i;
    let K_scalar = crate::ccykc::natural_to_bytes(&(&weight_KU_i * &e_beta_i));
    let KU_i_scalar = crate::ccykc::natural_to_bytes(&(&weight_KU_i * &c));
    let R_KU_i_scalar = crate::ccykc::natural_to_bytes(&weight_KU_i);

    if CG::multiexp(
      class_group.identity_p(),
      &[
        (G, &crate::ccykc::natural_to_bytes(&G_scalar)),
        (class_group.f(), &crate::ccykc::natural_to_bytes(&H_scalar)),
        (&D_Z_i, &D_Z_i_scalar),
        (&Z_i, &Z_i_scalar),
        (&R_Z_i, &R_Z_i_scalar),
        (&D_K_i, &D_K_i_scalar),
        (&K_i, &K_i_scalar),
        (&R_K_i, &R_K_i_scalar),
        (&D_U_i, &D_U_i_scalar),
        (&U_i, &U_i_scalar),
        (&R_U_i, &R_U_i_scalar),
        (&D_ZU_i, &D_ZU_i_scalar),
        (Z, &Z_scalar),
        (&ZU_i, &ZU_i_scalar),
        (&R_ZU_i, &R_ZU_i_scalar),
        (&D_KU_i, &D_KU_i_scalar),
        (K, &K_scalar),
        (&KU_i, &KU_i_scalar),
        (&R_KU_i, &R_KU_i_scalar),
        (neg_U, &crate::ccykc::natural_to_bytes(&neg_U_scalar)),
      ],
    ) != *class_group.identity_p()
    {
      Err(io::Error::other("invalid proof"))?;
    }

    Ok(())
  }
}
