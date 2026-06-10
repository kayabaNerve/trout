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

use alloc::{vec::Vec, vec};

use rand::{TryRng, TryCryptoRng, Rng as _, CryptoRng};

use crypto_bigint::{
  CtGt, CtAssign, Zero, One, NonZero, Odd, Limb, CheckedAdd, CheckedSub, Mul, ConcatenatingMul,
  ConcatenatingSquare, Div, Rem, NegMod, MulMod, SquareMod, BitOps, Encoding, RandomBits,
  RandomMod, UnsignedWithMontyForm, Integer, BoxedUint,
};

use class_groups::{
  FundamentalDiscriminant as _, NegativeDiscriminant as _, Cl15Error, Cl15p, Element,
  CryptoBigintElement, Table,
};

use cshake::digest::{CustomizedInit as _, Update as _, ExtendableOutput as _, XofReader};

use crate::WrappedGroup;

/// The non-interactive setup which MUST be run before the interactive setup, signing protocol.
pub struct NonInteractiveSetup<Up, Up2, Udk, Udp> {
  context: Vec<u8>,
  cl15p: Cl15p<Up, Up2, Udk, Udp>,
  generator_k: CryptoBigintElement<BoxedUint>,
  generator_p: CryptoBigintElement<BoxedUint>,
}

impl<Up: BitOps + Encoding, Up2, Udk: Encoding, Udp: Encoding>
  NonInteractiveSetup<Up, Up2, Udk, Udp>
{
  /// Inject a point from the class group of fundamental discriminant to the class group of
  /// non-fundamental discriminant, before scaling it by `p`.
  pub(crate) fn inject_p<E: Element>(cl15p: &Cl15p<Up, Up2, Udk, Udp>, e: impl Element) -> E {
    let p = cl15p.fundamental_discriminant().p();
    let base = cl15p.fundamental_discriminant().inject::<E>(e, p);

    // TODO: `Table::new`
    Table::msm_vartime(
      E::identity(cl15p.absolute_value()),
      &[(p.to_le_bytes().as_ref(), &Table::new(core::num::NonZero::new(4).unwrap(), base))],
    )
  }
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
    + BitOps
    + Encoding
    + RandomBits
    + Integer,
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
where
  <Udk as ConcatenatingMul<<Up as ConcatenatingSquare>::Output>>::Output: Encoding,
{
  /// Perform the non-interactive setup.
  ///
  /// The context string MUST be either:
  /// - The compressed encoding of the ECDSA signing key, if key derivations are not used
  /// - The sequential compressed encodings of the two keys used for key derivation,
  ///   if key derivations are used
  ///
  /// The domain-separation tag is used as the customization for cSHAKE (without a function name).
  /// The 16-bit little-endian encoding of the fundamental discriminant's bit-length is absorbed
  /// into the sponge, followed by the context string (with no delineation or demarcation). The
  /// sponge is squeezed for $\lceil (2 * \mathsf{G::BITS_OF_SECURITY}) / 8 \rceil$ bytes to form a
  /// binding context string to be used as the domain-separation tag for future invocations of
  /// cSHAKE, itself assumed binding to the ciphersuite, inputs, _and_ the further squeezes of the
  /// sponge.
  ///
  /// The sponge is then squeezed to find two numbers:
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
  /// $\mathsf{next_prime_ideal_squared}(a', \Delta_k)$ is invoked to obtain a generator of the
  /// class group with discriminant $\Delta_k$. This is then injected to obtain a corresponding
  /// generator of the class group with discriminant $\Delta_p$.
  ///
  /// The `rng` argument is not used to perform the setup other than as entropy for primality
  /// tests. Specifying different RNGs will NOT affect the result, other than with negligible
  /// probability.
  pub fn setup<G: WrappedGroup<Up = Up>>(
    mut rng: impl CryptoRng,
    context: impl IntoIterator<Item = impl AsRef<[u8]>>,
    fundamental_discriminant_bit_length: u16,
  ) -> Result<Self, Cl15Error> {
    const {
      match <G::CShake as crate::CShake>::BITS_OF_SECURITY {
        256 => {
          assert!(G::BITS_OF_SECURITY > 128);
          assert!(G::BITS_OF_SECURITY <= 256);
        }
        128 => {
          assert!(G::BITS_OF_SECURITY <= 128);
        }
        _ => panic!("unrecognized bits of security for cSHAKE"),
      }
    }

    let mut sponge = G::CShake::new_customized(G::DST);
    sponge.update(&fundamental_discriminant_bit_length.to_le_bytes());
    for context_piece in context {
      sponge.update(context_piece.as_ref());
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
      fn try_fill_bytes(&mut self, bytes: &mut [u8]) -> Result<(), Self::Error> {
        self.0.read(bytes);
        Ok(())
      }
    }
    impl<X: XofReader> TryCryptoRng for XofRand<X> {}
    let mut sponge = XofRand(sponge);

    let mut context = vec![
      0;
      usize::from(
        u16::try_from((2 * u32::from(G::BITS_OF_SECURITY)).div_ceil(8))
          .expect(r"$\lceil (2 * x) / 8 \rceil \le x$")
      )
    ];
    sponge.fill_bytes(&mut context);

    // Map from the order of the elliptic curve to `Up`
    let p = Odd::new(crate::p_Up::<Up, G>()).unwrap();

    let cl15k_parameters =
      Cl15p::sample_parameters(u32::from(fundamental_discriminant_bit_length), &p)?;
    let q_apostraphe =
      Option::<_>::from(cl15k_parameters.sample_q_apostraphe(&mut sponge)).ok_or(Cl15Error::NoQ)?;
    let cl15p = Cl15p::derive(
      &mut rng,
      u32::from(G::BITS_OF_SECURITY),
      u32::from(fundamental_discriminant_bit_length),
      p,
      q_apostraphe,
    )?;

    let floor_sqrt_delta_div_4 = (BoxedUint::from_le_bytes(
      cl15p.fundamental_discriminant().absolute_value().as_ref().into(),
    ) >> 2u32)
      .floor_sqrt();
    let prime_ideal_seed = {
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
      u32::from(G::BITS_OF_SECURITY),
    );

    let generator_p = Self::inject_p(&cl15p, generator_k.clone());

    Ok(Self { context, cl15p, generator_k, generator_p })
  }
}

impl<Up, Up2, Udk, Udp> NonInteractiveSetup<Up, Up2, Udk, Udp> {
  /// The context.
  ///
  /// This is binding to the ECDSA signing key when key derivations are NOT used, or binding to the
  /// two values used to derive the ECDSA signing key, and the result of the non-interactive setup
  /// protocol (as accessible via methods on this object).
  pub fn context(&self) -> &[u8] {
    &self.context
  }

  /// The CL15 discriminants.
  pub fn cl15p(&self) -> &Cl15p<Up, Up2, Udk, Udp> {
    &self.cl15p
  }
  /// A generator of the class group with discriminant $\Delta_k$.
  pub fn generator_k(&self) -> &CryptoBigintElement<BoxedUint> {
    &self.generator_k
  }
  /// A generator of the class group with discriminant $\Delta_p$.
  pub fn generator_p(&self) -> &CryptoBigintElement<BoxedUint> {
    &self.generator_p
  }
}
