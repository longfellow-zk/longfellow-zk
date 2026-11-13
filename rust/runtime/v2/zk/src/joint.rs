// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Selected joint commitments and circuit metadata for v2 composition.
use super::{
    context::{prepare_circuit_layout, InputLayout},
    packing_commitment::PackingCommitment,
    CircuitGeometry, ZkContext,
};
pub use crate::runtime::v2::proto::zk::CircuitProof;
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{EvaluationDomain, PackingExtension, PackingField, ZkField},
        v2::{
            polygero::{PolygeroConfig, PolygeroParam},
            proto::{polygero::PolygeroGeometry, Digest},
            witness_selection,
        },
    },
};

/// One frontend's full committed cell vector. The sibling selection protocol
/// owns the two extra masks; they are never logical circuit inputs.
pub struct SelectedField<'a, const W: usize, F: ZkField<W>, D, L = ()> {
    selection: witness_selection::Field<'a, W, F, D>,
    geometry: PolygeroGeometry,
    layout: L,
}
impl<const W: usize, F: ZkField<W>, D, L: Clone> Clone for SelectedField<'_, W, F, D, L> {
    fn clone(&self) -> Self {
        Self {
            selection: self.selection.clone(),
            geometry: self.geometry,
            layout: self.layout.clone(),
        }
    }
}
impl<'a, const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>> SelectedField<'a, W, F, D> {
    /// Derive the augmented backend geometry from the original frontend cells.
    pub fn new(
        cells: usize,
        config: PolygeroConfig,
        domain: &'a D,
        field_id: Vec<u8>,
    ) -> Result<Self, String> {
        Self::from_parameter(prepare_parameter(cells, config, domain)?, domain, field_id)
    }
    pub(crate) fn from_parameter(
        param: PolygeroParam,
        domain: &'a D,
        field_id: Vec<u8>,
    ) -> Result<Self, String> {
        let geometry = param.geometry();
        Ok(Self {
            selection: witness_selection::Field::new(param, domain, field_id)?,
            geometry,
            layout: (),
        })
    }
}

impl<'a, const W: usize, F: ZkField<W>, D, L> SelectedField<'a, W, F, D, L> {
    pub(crate) fn with_layout<A>(self, layout: A) -> SelectedField<'a, W, F, D, A> {
        SelectedField {
            selection: self.selection,
            geometry: self.geometry,
            layout,
        }
    }
    pub fn geometry(&self) -> PolygeroGeometry {
        self.geometry
    }
}

pub(crate) fn prepare_parameter<const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>>(
    cells: usize,
    config: PolygeroConfig,
    domain: &D,
) -> Result<PolygeroParam, String> {
    PolygeroParam::try_new(witness_selection::witness_count(cells)?, config, domain)
        .map_err(|e| e.to_string())
}

/// Frontend metadata consumed internally before the fingerprint round.
pub(crate) trait AbsorbLayout {
    fn absorb_layout(&self, t: &mut crate::runtime::v2::transcript::TranscriptRef<'_>);
}

impl AbsorbLayout for () {
    fn absorb_layout(&self, _: &mut crate::runtime::v2::transcript::TranscriptRef<'_>) {}
}
impl<L: AbsorbLayout> AbsorbLayout for &L {
    fn absorb_layout(&self, t: &mut crate::runtime::v2::transcript::TranscriptRef<'_>) {
        (*self).absorb_layout(t);
    }
}

// The private supertrait both seals the tuple traversal and keeps absorption
// inaccessible to callers; commit/receive are its only entry points.
pub(crate) trait AbsorbLayouts {
    fn absorb_layouts(&self, t: &mut crate::runtime::v2::transcript::TranscriptRef<'_>);
}
/// A typed list `(SelectedField, Tail)` ending in `()`. This conversion only
/// supplies frontend metadata; all fingerprint arithmetic stays in its sibling.
///
/// ```compile_fail,E0624
/// use longfellow_zk::runtime::v2::{zk::joint::Fields, transcript::TranscriptRef};
/// fn cannot_absorb_twice<L: Fields>(fields: &L, t: &mut TranscriptRef<'_>) {
///     fields.absorb_layouts(t);
/// }
/// ```
#[allow(private_bounds)]
pub trait Fields: AbsorbLayouts + Clone {
    type Selection: witness_selection::Fields;
    fn selection(&self) -> Self::Selection;
}
impl AbsorbLayouts for () {
    fn absorb_layouts(&self, _: &mut crate::runtime::v2::transcript::TranscriptRef<'_>) {}
}
impl Fields for () {
    type Selection = ();
    fn selection(&self) {}
}
impl<
        'a,
        const W: usize,
        F: ZkField<W>,
        D: EvaluationDomain<W, F>,
        L: AbsorbLayout + Clone,
        T: Fields,
    > Fields for (SelectedField<'a, W, F, D, L>, T)
{
    type Selection = (witness_selection::Field<'a, W, F, D>, T::Selection);
    fn selection(&self) -> Self::Selection {
        (self.0.selection.clone(), self.1.selection())
    }
}
impl<
        'a,
        const W: usize,
        F: ZkField<W>,
        D: EvaluationDomain<W, F>,
        L: AbsorbLayout + Clone,
        T: Fields,
    > AbsorbLayouts for (SelectedField<'a, W, F, D, L>, T)
{
    fn absorb_layouts(&self, t: &mut crate::runtime::v2::transcript::TranscriptRef<'_>) {
        self.0.layout.absorb_layout(t);
        self.1.absorb_layouts(t);
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
    fields: L,
}
impl<L: Fields> JointParam<L> {
    pub fn new(fields: L) -> Result<Self, String> {
        Ok(Self {
            selection: witness_selection::Param::new(fields.selection())?,
            fields,
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
/// Joint commit/receive absorbs each participant's layout before the fingerprint round.
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
    pub(super) inputs: InputLayout,
    /// Values not all native: the split layout. `None` is all native.
    pub(super) storage: Option<super::split::Split>,
}
impl<const W: usize, F: ZkField<W> + PackingField> CircuitParticipant<W, F> {
    /// Prove `circuits` as one layered sumcheck; `circuits[0]` is the primary
    /// circuit. They share the public prefix and read prefixes of one input
    /// array. Each intermediate layer has one wire array; only the sparse quad
    /// terms retain their local indexing.
    ///
    /// The last `virtual_inputs` entries of the shared input array are virtual:
    /// each proof defines them as affine functions of committed inputs (see
    /// `VirtualInputs`). The primary circuit cannot read them; the other
    /// components may.
    pub fn new<D: EvaluationDomain<W, F>>(
        circuits: &[&Circuit<F>],
        virtual_inputs: usize,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        let (circuit, others) = circuits.split_first().ok_or("empty circuit list")?;
        let (geometry, param, backend) = prepare_circuit_layout(
            circuit,
            others,
            virtual_inputs,
            config,
            ctx.field().packing_extension(),
            ctx,
        )?;
        Ok(Self {
            geometry,
            #[cfg(any(test, feature = "prover"))]
            config,
            param,
            backend,
            id: circuit.id,
            additional_ids: others.iter().map(|c| c.id).collect(),
            inputs: InputLayout::new(circuits, virtual_inputs)?,
            storage: None,
        })
    }
    /// A single-circuit participant whose values `[private inputs | pads]` are
    /// stored as `storage` says. With some native values (mixed storage), it
    /// commits `[native private inputs | R | pads]` and `mask` holds R's bits
    /// in the binary commitment. With none (pure foreign storage), it commits
    /// nothing and `mask` is `None`.
    pub fn with_storage<D: EvaluationDomain<W, F>>(
        circuit: &Circuit<F>,
        storage: super::storage::StorageMap,
        mask: Option<super::storage::Group>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, String> {
        let extension = ctx.field().packing_extension();
        if ctx.field().is_binary() || extension.degree() != 1 {
            return Err("split storage requires a degree-one prime frontend".into());
        }
        let sc_geom = crate::runtime::v2::sumcheck::circuit_geometry(&[circuit])?;
        let inputs = InputLayout::new(&[circuit], 0)?;
        let private = inputs.committed();
        let values = private
            .checked_add(sc_geom.pad_count()?)
            .ok_or("split layout overflow")?;
        let split = super::split::layout(storage, mask, private, values)?;
        // Mixed storage commits the native private inputs, then R, then pads;
        // pure foreign storage commits nothing.
        let committed = if split.mask.is_some() {
            split.mask_cell + 1
        } else {
            0
        };
        let pads = if split.mask.is_some() {
            sc_geom.pad_count()?
        } else {
            0
        };
        let layout = super::packing_commitment::PackingLayout::new(committed, pads, 1)?;
        let param = prepare_parameter(layout.witness_count, config, ctx.domain)?;
        let selected =
            SelectedField::from_parameter(param.clone(), ctx.domain, ctx.field().packing_id())?;
        Ok(Self {
            geometry: CircuitGeometry {
                sc_geom,
                com_geom: selected.geometry(),
                packing_degree: 1,
            },
            #[cfg(any(test, feature = "prover"))]
            config,
            param,
            backend: PackingCommitment::new(ctx.field().clone(), layout, extension)?,
            id: circuit.id,
            additional_ids: Vec::new(),
            inputs,
            storage: Some(split),
        })
    }
    /// Whether this participant commits any cells to the joint opening.
    pub fn commits(&self) -> bool {
        !self.storage.as_ref().is_some_and(|s| s.mask.is_none())
    }
    pub fn input_layout(&self) -> InputLayout {
        self.inputs
    }
    /// Check that `circuits` are this participant's circuits, in order, and
    /// that `public` inputs fit the primary circuit.
    pub(super) fn validate_circuits(
        &self,
        circuits: &[&Circuit<F>],
        public: usize,
    ) -> Result<(), String> {
        let (circuit, others) = circuits.split_first().ok_or("empty circuit list")?;
        if public != circuit.raw.npublic_input {
            return Err("public inputs length mismatch".into());
        }
        if circuit.id != self.id
            || self.additional_ids.len() != others.len()
            || self
                .additional_ids
                .iter()
                .zip(others)
                .any(|(id, c)| *id != c.id)
        {
            return Err("circuit statement mismatch".into());
        }
        if InputLayout::new(circuits, self.inputs.virtual_count())? != self.inputs {
            return Err("shared input layout mismatch".into());
        }
        Ok(())
    }
    pub fn geometry(&self) -> CircuitGeometry {
        self.geometry.clone()
    }
    pub fn participant<'a, D: EvaluationDomain<W, F>>(
        &'a self,
        ctx: &ZkContext<'a, W, F, D>,
    ) -> Result<SelectedField<'a, W, F, D, &'a Self>, String> {
        Ok(
            SelectedField::from_parameter(
                self.param.clone(),
                ctx.domain,
                ctx.field().packing_id(),
            )?
            .with_layout(self),
        )
    }
}

#[cfg(test)]
#[path = "../tests/circuits.rs"]
mod tests;
