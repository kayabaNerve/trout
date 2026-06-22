use alloc::{vec::Vec, vec};
use std::io;

use group::{ff::Field as _, Group};

use crypto_bigint::{NonZero, Limb, Encoding, BoxedUint};
use class_groups::{FundamentalDiscriminant as _, NegativeDiscriminant as _, Element, Table};

use crate::{WrappedGroup, Up2, NonInteractiveSetup};

/// A batch verifier for zero-knowledge proofs.
///
/// This verifies that the multi-scalar multiplication of the terms over the class group with
/// fundamental discriminant $\Delta_k$, then injected into the class group with non-fundamental
/// discriminant $|Delta_p$ and scaled by $p$, sum with the multi-scalar multiplication of the
/// terms over the class group with non-fundamental discriminant $|Delta_p$ to the identity, and
/// that the multi-scalar multiplication of the terms over the elliptic curve sum to the identity.
#[must_use]
pub(crate) struct BatchVerifier<E, G: WrappedGroup> {
  /// The scalar for the `generator_k` from the setup.
  pub(crate) generator_k: BoxedUint,
  /// The terms over the class group with fundamental discriminant $\Delta_k$.
  pub(crate) k: Vec<(BoxedUint, Table<E>)>,

  /// The scalar for the generator of the `p`-order subgroup in the class group with
  /// non-fundamental discriminant $\Delta_p$.
  pub(crate) f: <G::G as Group>::Scalar,
  /// The scalar for the `generator_p` from the setup.
  pub(crate) generator_p: BoxedUint,
  /// The terms over the class group with non-fundamental discriminant $\Delta_p$.
  pub(crate) p: Vec<(BoxedUint, Table<E>)>,

  /// The scalar for the `generator_e` from the specified group.
  pub(crate) generator_e: <G::G as Group>::Scalar,
  /// The terms over the elliptic curve.
  pub(crate) e: Vec<(<G::G as Group>::Scalar, G::G)>,
}

impl<E: Clone, G: WrappedGroup> Clone for BatchVerifier<E, G> {
  fn clone(&self) -> Self {
    let Self { generator_k, k, generator_p, p, f, generator_e, e } = self;
    Self {
      generator_k: generator_k.clone(),
      k: k.clone(),
      generator_p: generator_p.clone(),
      p: p.clone(),
      f: *f,
      generator_e: *generator_e,
      e: e.clone(),
    }
  }
}

impl<E, G: WrappedGroup> BatchVerifier<E, G> {
  pub(crate) fn new() -> Self {
    Self {
      generator_k: BoxedUint::zero(),
      k: vec![],

      f: <G::G as Group>::Scalar::ZERO,
      generator_p: BoxedUint::zero(),
      p: vec![],

      generator_e: <G::G as Group>::Scalar::ZERO,
      e: vec![],
    }
  }
}

impl<E: Element, G: WrappedGroup> BatchVerifier<E, G> {
  /*
    TODO: Optimize this.

    This ad-hoc generates tables when it should be using provided tables. In doing so, it keeps
    allocating new buffers to store representations in.

    This doesn't apply any multi-scalar multiplication optimizations over the elliptic curve.
  */
  pub(crate) fn verify<Udk: Clone + AsMut<[Limb]> + Encoding, Udp: Encoding>(
    self,
    setup: &NonInteractiveSetup<G::Up, Up2<G>, Udk, Udp>,
  ) -> io::Result<()> {
    let Self { generator_k, k, generator_p, p, f, generator_e, e } = self;

    let table = |(scalar, element): (BoxedUint, E)| {
      (scalar, Table::new(core::num::NonZero::new(4).unwrap(), element))
    };
    let scalar = |(scalar, element): (BoxedUint, Table<E>)| (scalar.to_le_bytes(), element);

    let k = core::iter::once((generator_k, E::from(setup.generator_k().clone())))
      .map(table)
      .chain(k)
      .map(scalar)
      .collect::<Vec<_>>();
    let k = k.iter().map(|(scalar, table)| (scalar.as_ref(), table)).collect::<Vec<_>>();
    let k = Table::msm_vartime(
      E::identity(setup.cl15p().fundamental_discriminant().absolute_value()),
      &k,
    );

    let p = core::iter::once((generator_p, E::from(setup.generator_p().clone())))
      .chain(core::iter::once((
        crate::p_Up::<BoxedUint, G>(),
        setup.cl15p().fundamental_discriminant().inject::<_, BoxedUint, _>(
          k,
          &NonZero::new(BoxedUint::from(<_ as AsRef<[Limb]>>::as_ref(
            setup.cl15p().fundamental_discriminant().p().as_ref(),
          )))
          .unwrap(),
        ),
      )))
      .map(table)
      .chain(p)
      .map(scalar)
      .collect::<Vec<_>>();
    let p = p.iter().map(|(scalar, table)| (scalar.as_ref(), table)).collect::<Vec<_>>();
    if bool::from(
      !Table::msm_vartime(E::identity(setup.cl15p().absolute_value()), &p)
        .add(setup.cl15p().f_scaled::<E>(&crate::Up_from_scalar::<G::Up, G>(&f)))
        .is_identity(),
    ) {
      Err(io::Error::other("elements did not sum to the identity"))?;
    }

    if bool::from(
      !core::iter::once((generator_e, G::generator_e()))
        .chain(e)
        .map(|(scalar, generator)| generator * scalar)
        .sum::<G::G>()
        .is_identity(),
    ) {
      Err(io::Error::other("points did not sum to the identity"))?;
    }

    Ok(())
  }
}
