// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Pure-foreign storage for circuits whose values live in the binary commitment.
//!
//! Every value `[private inputs | pads]` of the participant is a bit group of
//! the binary commitment, so it commits nothing and has no Polygero
//! parameter, masks or rows. After its frontend, fresh row weights, drawn and
//! used by the pure split step (`PureClaim::batch`), batch every layer row
//! and the input equation into one foreign claim with a public target
//! (`batching`). Application drivers may expand that linear claim into
//! committed coordinates before passing it to the foreign adapter.
#[cfg(test)]
use super::super::storage::{ModularClaim, Storage};
use super::{
    super::{
        batching::{self, LinearClaim},
        joint::{Frontend, FrontendPart, Participant, StorageLayout},
        packing_commitment::PackingLayout,
        storage::StorageMap,
    },
    transcript, SplitShape,
};
#[cfg(test)]
use crate::runtime::v2::polygero::PolygeroParam;
use crate::{
    core::{algebra::BareField, proto::v2::Circuit},
    runtime::{
        algebra::{packing::PackingField, range_interpolation::EvaluationDomain, ZkField},
        v2::{
            polygero::PolygeroLinearTerm,
            proto::{polygero::PolygeroConfig, sumcheck::SumcheckProof, zk::CircuitProofGeometry},
            sumcheck,
            transcript::Bound,
        },
    },
};

/// A participant with pure-foreign storage: a single degree-one prime
/// circuit all of whose values are bit groups of the binary commitment.
pub(crate) struct PureSplit<F: ZkField + PackingField> {
    pub(super) frontend: Frontend<F>,
    pub(super) map: StorageMap,
}
impl<F: ZkField + PackingField> PureSplit<F> {
    /// The pure-foreign participant of `circuit` whose values are stored as
    /// `map` says; every value must be foreign.
    pub(crate) fn new<D: EvaluationDomain<F>>(
        circuit: &Circuit<F>,
        map: StorageMap,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, String> {
        let shape = SplitShape::new(circuit, domain)?;
        map.check_pure(shape.values)?;
        let layout = PackingLayout::new(0, 0, 1)?;
        Ok(Self {
            frontend: shape.frontend(circuit, layout, 0, config, domain)?,
            map,
        })
    }
    pub(crate) fn geometry(&self) -> CircuitProofGeometry {
        self.frontend.geometry.clone()
    }
    #[cfg(feature = "mdoc")]
    pub(crate) fn field(&self) -> &F {
        self.frontend.field()
    }
    /// The whole claim of this participant, whose target is public: the
    /// batched claim `claim` over its foreign values.
    #[cfg(test)]
    fn claim(&self, claim: LinearClaim<F::E>) -> Result<ModularClaim<F::E>, String> {
        if claim.weights.len() != self.map.entries().len() {
            return Err("pure claim does not cover the participant's values".into());
        }
        // `new` checked that every value is foreign.
        let terms = self
            .map
            .entries()
            .iter()
            .zip(&claim.weights)
            .filter_map(|(s, w)| match s {
                Storage::Foreign(g) => Some((*g, w.clone())),
                Storage::Native(_) => None,
            })
            .collect();
        Ok(ModularClaim {
            terms,
            target: claim.target,
        })
    }
}
impl<F: ZkField + PackingField> Participant<F> for PureSplit<F> {
    fn frontend(&self) -> &Frontend<F> {
        &self.frontend
    }
    fn storage(&self) -> StorageLayout<'_> {
        StorageLayout::Pure(&self.map)
    }
    #[cfg(test)]
    fn param_for_test(&self) -> Option<&PolygeroParam> {
        None
    }
}

/// A pure-foreign participant's frontend claim over `[private inputs |
/// pads]`: the layer rows and the input equation, unbatched.
pub(crate) struct PureClaim<E> {
    rows: (Vec<PolygeroLinearTerm<E>>, Vec<E>),
    /// The input equation `<w, v> = t` over the values.
    pub(crate) claim: LinearClaim<E>,
}
/// The frontend's rows from its reduced constraints, on its values.
fn frontend_claim<F: ZkField + PackingField>(
    part: &FrontendPart<'_, F, PureSplit<F>>,
    constraints: sumcheck::symbolic::Constraints<F::E>,
) -> Result<PureClaim<F::E>, String> {
    let (rows, claim) = batching::rows(
        part.circuits()[0],
        &part.public,
        constraints,
        part.frontend().geometry.sumcheck(),
        part.field(),
    )?;
    Ok(PureClaim { rows, claim })
}

impl<E> PureClaim<E> {
    /// The number of row weights: one per layer row, one for the input
    /// equation.
    pub(crate) fn row_weight_count(&self) -> usize {
        self.rows.1.len() + 1
    }
    /// Draw the row weights rho_0..rho_L at the current boundary, right after
    /// the frontend's last message, and batch every row and the input
    /// equation with them into one foreign claim with a public target. The
    /// weights are internal to this step (transcript I8).
    #[cfg(test)]
    pub(crate) fn batch<F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, F, PureSplit<F>>>,
    ) -> Result<ModularClaim<E>, String>
    where
        F: ZkField + PackingField + BareField<E = E>,
    {
        let p = t.part().participant;
        p.claim(self.batch_linear(t)?)
    }
    /// Batch this pure frontend on its bound session before affine coordinate expansion.
    pub(crate) fn batch_linear<F>(
        self,
        t: &mut Bound<'_, FrontendPart<'_, F, PureSplit<F>>>,
    ) -> Result<LinearClaim<E>, String>
    where
        F: ZkField + PackingField + BareField<E = E>,
    {
        let f = t.part().field();
        let weights = transcript::row_weights(&mut t.transcript(), self.row_weight_count(), f);
        batching::batch((self.rows, self.claim), &weights, f)
    }
}

cfg_prover! {pub(crate) mod prover;}
cfg_verifier! {pub(crate) mod verifier;}
