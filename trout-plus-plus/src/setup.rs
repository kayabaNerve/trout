//! Trout++ Setup Protocol
//!
//! Trout++ begins with a _non-interactive_ setup protocol to sample the discriminant(s) of the
//! class groups which will be used with the Trout++ protocol. This requires a context string and
//! the parameters for the class group itself. This non-interactive setup protocol MUST be run
//! before the actual setup protocol, or the signing protocol, is run.
//!
//! Trout++ continues with a one-round _interactive_ setup protocol for an existing
//! Shamir-secret-shared signing key. Callers MAY perform the interactive setup protocol ahead of
//! time or MAY perform it simultaneously with the first round of the signing protocol, both
//! exhibiting the same complexities, to avoid an explicit additional setup and to avoid having to
//! store the results of the setup protocol. Similarly, Callers MAY perform the interactive setup
//! protocol for a securely-derived signing key or MAY perform the interactive setup protocol for a
//! pair of keys and then perform derivation over the setups (meaning the same setups can be reused
//! even when performing signing for derivations).

use rand::{TryRng, TryCryptoRng, Rng as _, CryptoRng};

use ::crypto_bigint::{
  Choice, CtOption, CtGt, CtAssign, Zero, One, NonZero, Odd, Limb, CheckedAdd, CheckedSub, Mul,
  ConcatenatingMul, ConcatenatingSquare, Div, Rem, NegMod, MulMod, SquareMod, BitOps, Encoding,
  RandomBits, RandomMod, UnsignedWithMontyForm, BoxedUint,
};

use class_groups::{NegativeDiscriminant as _, Cl15Error, Cl15p, Element as _, CryptoBigintElement};

use cshake::{
  digest::{Update as _, ExtendableOutput as _, XofReader},
  CShake,
};

/// The non-interactive setup which MUST be run before the interactive setup, signing protocol.
pub struct NonInteractiveSetup<Up, Up2, Udk, Udp> {
  cl15p: Cl15p<Up, Up2, Udk, Udp>,
  generator_k: CryptoBigintElement<BoxedUint>,
}

impl<
  Up: Clone
    + AsRef<[Limb]>
    + AsMut<[Limb]>
    + CtAssign
    + Zero
    + One
    + NegMod<Output = Up>
    + MulMod<Output = Up>
    + SquareMod<Output = Up>
    + ConcatenatingSquare
    + BitOps,
  Udk: Clone
    + AsRef<[Limb]>
    + AsMut<[Limb]>
    + CtGt
    + One
    + CheckedAdd
    + CheckedSub<Udk>
    + for<'a> Mul<&'a Up, Output = Udk>
    // TODO: `for<'a> ConcatenatingMul<&'a <Up as ConcatenatingSquare>::Output, Output: 'static>`
    + ConcatenatingMul<<Up as ConcatenatingSquare>::Output>
    + for<'a> Div<&'a NonZero<Up>, Output = Udk>
    + for<'a> Rem<&'a NonZero<Up>, Output = Up>
    + BitOps
    + Encoding
    + RandomBits
    + RandomMod
    + UnsignedWithMontyForm,
>
  NonInteractiveSetup<
    Up,
    <Up as ConcatenatingSquare>::Output,
    Udk,
    <Udk as ConcatenatingMul<<Up as ConcatenatingSquare>::Output>>::Output,
  >
{
  /// Perform the non-interactive setup.
  ///
  /// This requires a domain-separation tag followed by the context. The domain-separation tag
  /// MUST be a recognized label for an elliptic curve ("P-224", "P-256", "P-384", "P-521").
  /// The context string MUST be either:
  /// - The compressed encoding of the ECDSA signing key, if key derivations are not used
  /// - The concatenated compressed encodings of the two keys used for key derivation,
  ///   if key derivations are used
  ///
  /// The domain-separation tag is used as the customization for cSHAKE (without a function name),
  /// where the context string is absorbed before the sponge is squeezed to find two numbers:
  /// - `q'`, an integer in range $0 \le q' \le (q_\mathsf{max} - q_\mathsf{min})$, where
  ///   $q_\mathsf{max}$ (respectively $q_\mathsf{min}$) is the largest (respectively smallest)
  ///   integer such that
  ///   $\lfloor \mathsf{log}_2(p * q_{*}) \rfloor + 1 = \mathsf{fundamental_discriminant_bits}$.
  /// - `a'`, an integer in range $0 \le a' \le \sqrt((-\Delta_k) / 4)$.
  ///
  /// The process occurs via rejection sampling, where for a $k$-bit sample, $\lceil k / 8 \rceil$
  /// bytes are squeezed. If the bytes, decoded as a little-endian integer, are in the sample
  /// range, they're accepted. Else, a new sample occurs.
  ///
  /// The prime $q$ is decided as the first eligible prime number found by testing (and
  /// incrementing by $1$ from) $q_\mathsf{min} + q'$. If the current value is equal to
  /// $q_\mathsf{max}$, the current value is 'incremented' to $q_\mathsf{min}$.
  ///
  /// $\mathsf{next_prime_ideal_squared}(a', \Delta_k)$ is invoked for a generator of the class
  /// group with discriminant $\Delta_k$.
  ///
  /// `CSHAKE_RATE` MUST be `136` (for cSHAKE 256) or `168` (for cSHAKE 128). The bits of security
  /// from cSHAKE MUST be greater than or equal to `bits_of_security`.
  ///
  /// The `rng` argument is not used to perform the setup other than as entropy for primality
  /// tests. Specifying different RNGs will NOT affect the result, other than with negligible
  /// probability.
  pub fn setup<'context, const CSHAKE_RATE: usize>(
    mut rng: impl CryptoRng,
    dst: &[u8],
    context: impl IntoIterator<Item = &'context [u8]>,
    p: Odd<Up>,
    bits_of_security: u32,
    fundamental_discriminant_bit_length: u32,
  ) -> Result<Self, Cl15Error> {
    {
      let cshake_bits_of_security = match CSHAKE_RATE {
        136 => 256,
        168 => 128,
        _ => panic!("unrecognized rate for cSHAKE"),
      };
      assert!(bits_of_security >= cshake_bits_of_security);
    }

    let mut sponge = CShake::<CSHAKE_RATE>::new_with_function_name(&[], dst);
    for context_piece in context {
      sponge.update(context_piece);
    }
    let sponge = sponge.finalize_xof();

    struct XofRand<X: XofReader>(X);
    impl<X: XofReader> TryRng for XofRand<X> {
      type Error = core::convert::Infallible;
      fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut bytes = [0; 4];
        self.0.read(&mut bytes);
        Ok(u32::from_le_bytes(bytes))
      }
      fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut bytes = [0; 8];
        self.0.read(&mut bytes);
        Ok(u64::from_le_bytes(bytes))
      }
      fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        self.0.read(dst);
        Ok(())
      }
    }
    impl<X: XofReader> TryCryptoRng for XofRand<X> {}
    let mut sponge = XofRand(sponge);

    let cl15k_parameters = Cl15p::sample_parameters(fundamental_discriminant_bit_length, &p)?;
    let q_apostraphe =
      Option::<_>::from(cl15k_parameters.sample_q_apostraphe(&mut sponge)).ok_or(Cl15Error::NoQ)?;
    let cl15p = Cl15p::derive(
      &mut rng,
      bits_of_security,
      fundamental_discriminant_bit_length,
      p,
      q_apostraphe,
    )?;

    let floor_sqrt_delta_div_4 = (BoxedUint::from_le_bytes(
      cl15p.fundamental_discriminant().absolute_value().as_ref().into(),
    ) >> 2u32)
      .floor_sqrt();
    let mut prime_ideal_seed = {
      let mut bytes = vec![0; usize::try_from(floor_sqrt_delta_div_4.bits().div_ceil(8)).unwrap()];
      while {
        sponge.fill_bytes(&mut bytes);
        BoxedUint::from_le_bytes(bytes.clone().into()) > floor_sqrt_delta_div_4
      } {}
      BoxedUint::from_le_bytes(bytes.into())
    };
    let generator_k = CryptoBigintElement::<BoxedUint>::next_prime_ideal_squared(
      rng,
      prime_ideal_seed,
      cl15p.fundamental_discriminant().absolute_value(),
      bits_of_security,
    );

    Ok(Self { cl15p, generator_k })
  }
}
