// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Selected joint commitments and circuit metadata for v2 composition.
use super::{
    context::prepare_circuit_layout, packing_commitment::PackingCommitment, CircuitGeometry,
    ZkContext,
};
pub use crate::runtime::proto::zk_v2::CircuitProof;
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingField, ZkField},
        polygero::{PolygeroConfig, PolygeroParam},
        proto::{polygero::PolygeroGeometry, Digest},
        witness_selection,
    },
};

/// One frontend's full committed cell vector. The sibling selection protocol
/// owns the two extra masks; they are never logical circuit inputs.
pub struct SelectedField<'a, const W: usize, F: ZkField<W>, D> {
    selection: witness_selection::Field<'a, W, F, D>,
    geometry: PolygeroGeometry,
}
impl<const W: usize, F: ZkField<W>, D> Clone for SelectedField<'_, W, F, D> {
    fn clone(&self) -> Self {
        Self {
            selection: self.selection.clone(),
            geometry: self.geometry.clone(),
        }
    }
}
impl<'a, const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>> SelectedField<'a, W, F, D> {
    /// Derive the augmented backend geometry from the original frontend cells.
    pub fn new(
        cells: usize,
        config: PolygeroConfig,
        f: &'a F,
        domain: &'a D,
        field_id: Vec<u8>,
    ) -> Result<Self, String> {
        Self::from_parameter(
            prepare_parameter(cells, config, f, domain)?,
            f,
            domain,
            field_id,
        )
    }
    pub(crate) fn from_parameter(
        param: PolygeroParam,
        f: &'a F,
        domain: &'a D,
        field_id: Vec<u8>,
    ) -> Result<Self, String> {
        let geometry = param.geometry();
        Ok(Self {
            selection: witness_selection::Field::new(param, f, domain, field_id)?,
            geometry,
        })
    }
    pub fn geometry(&self) -> PolygeroGeometry {
        self.geometry.clone()
    }
}

pub(crate) fn prepare_parameter<const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>>(
    cells: usize,
    config: PolygeroConfig,
    f: &F,
    domain: &D,
) -> Result<PolygeroParam, String> {
    PolygeroParam::try_new(witness_selection::witness_count(cells)?, config, domain, f)
        .map_err(|e| e.to_string())
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for () {}
    impl<H, T: Sealed> Sealed for (H, T) {}
}

/// A typed list `(SelectedField, Tail)` ending in `()`. This conversion only
/// supplies frontend metadata; all fingerprint arithmetic stays in its sibling.
pub trait Fields: sealed::Sealed + Clone {
    type Selection: witness_selection::Fields;
    fn selection(&self) -> Self::Selection;
}
impl Fields for () {
    type Selection = ();
    fn selection(&self) {}
}
impl<'a, const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>, T: Fields> Fields
    for (SelectedField<'a, W, F, D>, T)
{
    type Selection = (witness_selection::Field<'a, W, F, D>, T::Selection);
    fn selection(&self) -> Self::Selection {
        (self.0.selection.clone(), self.1.selection())
    }
}
pub type Witnesses<L> = witness_selection::Witnesses<<L as Fields>::Selection>;
pub type Statements<L> = witness_selection::Statements<<L as Fields>::Selection>;
pub type Bodies<L> = witness_selection::Bodies<<L as Fields>::Selection>;
pub type Coefficients<L> = <<L as Fields>::Selection as witness_selection::Fields>::Coefficients;
pub type Responses<L> = <<L as Fields>::Selection as witness_selection::Fields>::Responses;

/// Zk-v2 owns the composition: receipt and commitment select the witness before
/// any frontend challenge, and completion necessarily authenticates those rows.
#[derive(Clone)]
pub struct JointParam<L: Fields> {
    selection: witness_selection::Param<L::Selection>,
}
impl<L: Fields> JointParam<L> {
    pub fn new(fields: L) -> Result<Self, String> {
        Ok(Self {
            selection: witness_selection::Param::new(fields.selection())?,
        })
    }
    pub fn context(&self) -> Digest {
        self.selection.context()
    }
    pub fn config(&self) -> PolygeroConfig {
        self.selection.config()
    }
}

cfg_prover! { #[path="joint_prover.rs"] mod prover; pub use prover::JointProver; }
cfg_verifier! { #[path="joint_verifier.rs"] mod verifier; pub use verifier::{Authenticated, JointVerifier}; }

/// A circuit's packing and commitment layout, independent of the participant list.
/// The application binds each participant before committing the shared column tree.
/// Input packing stays here; the lower-level Polygero participant only knows
/// full-field witness cells and affine constraints over them.
pub struct CircuitParticipant<const W: usize, F: ZkField<W> + PackingField> {
    pub(super) geometry: CircuitGeometry,
    #[cfg(any(test, feature = "prover"))]
    pub(super) config: PolygeroConfig,
    pub(super) param: PolygeroParam,
    pub(super) backend: PackingCommitment<F>,
    pub(super) id: [u8; 32],
    pub(super) additional_ids: Vec<[u8; 32]>,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        Self::with_circuits(circuit, &[], config, ctx)
    }
    /// Prove these circuits as one layered sumcheck. They share the same input
    /// counts and public/private ordering. Each intermediate layer has one wire
    /// array; only the sparse quad terms retain their circuit-local indexing.
    pub fn with_circuits<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        others: &[&Circuit<F>],
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        let (geometry, param, backend) =
            prepare_circuit_layout(circuit, others, config, ctx.f.packing_extension(), ctx)?;
        Ok(Self {
            geometry,
            #[cfg(any(test, feature = "prover"))]
            config,
            param,
            backend,
            id: circuit.id,
            additional_ids: others.iter().map(|c| c.id).collect(),
        })
    }
    pub(super) fn validate_circuits(
        &self,
        circuit: &Circuit<F>,
        public: usize,
        others: &[&Circuit<F>],
    ) -> Result<(), String> {
        if circuit.id != self.id
            || public != circuit.raw.npublic_input
            || self.additional_ids.len() != others.len()
        {
            return Err("joint circuit statement mismatch".into());
        }
        for (id, c) in self.additional_ids.iter().zip(others) {
            if *id != c.id
                || c.raw.ninput != circuit.raw.ninput
                || c.raw.npublic_input != circuit.raw.npublic_input
            {
                return Err("circuit statement or shared input layout mismatch".into());
            }
        }
        Ok(())
    }
    pub fn geometry(&self) -> CircuitGeometry {
        self.geometry.clone()
    }
    pub fn participant<'a, D: EvaluationDomain<W, F>>(
        &self,
        ctx: &ZkContext<'a, W, F, D>,
    ) -> Result<SelectedField<'a, W, F, D>, String> {
        SelectedField::from_parameter(self.param.clone(), ctx.f, ctx.domain, ctx.f.packing_id())
    }
}

#[cfg(test)]
#[path = "../tests/circuits.rs"]
mod tests;
