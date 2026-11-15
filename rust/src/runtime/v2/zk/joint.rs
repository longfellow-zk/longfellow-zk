// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Selected joint commitments and circuit metadata for v2 composition.
use std::borrow::Cow;

use super::{
    context::{prepare_circuit_layout, prepare_parameter, CircuitInput, InputLayout},
    packing_commitment::PackingCommitment,
    ZkContext,
};
use crate::{
    core::{algebra::RegisteredField, proto::v2::Circuit},
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            range_interpolation::EvaluationDomain,
            ZkField,
        },
        v2::{
            polygero::PolygeroParam,
            proto::{
                polygero::{PolygeroConfig, PolygeroGeometry},
                zk::CircuitGeometry,
            },
            sumcheck::{self, circuit_geometry, TopWeights},
            transcript::{Bound, Challenge},
            witness_selection,
        },
    },
};

/// One frontend's full committed cell vector. The sibling selection protocol
/// owns the two extra masks; they are never logical circuit inputs.
pub struct SelectedField<'a, const W: usize, F: ZkField<W> + RegisteredField, D> {
    selection: witness_selection::Field<'a, W, F, D>,
    geometry: PolygeroGeometry,
}
impl<const W: usize, F: ZkField<W> + RegisteredField, D> Clone for SelectedField<'_, W, F, D> {
    fn clone(&self) -> Self {
        Self {
            selection: self.selection.clone(),
            geometry: self.geometry,
        }
    }
}
impl<'a, const W: usize, F: ZkField<W> + RegisteredField, D: EvaluationDomain<W, F>>
    SelectedField<'a, W, F, D>
{
    /// Derive the augmented backend geometry from the original frontend cells.
    pub fn new(cells: usize, config: PolygeroConfig, domain: &'a D) -> Result<Self, String> {
        Self::from_parameter(prepare_parameter(cells, config, domain)?, domain)
    }
    fn from_parameter(param: PolygeroParam, domain: &'a D) -> Result<Self, String> {
        let geometry = param.geometry();
        Ok(Self {
            selection: witness_selection::Field::new(param, domain)?,
            geometry,
        })
    }
}

impl<const W: usize, F: ZkField<W> + RegisteredField, D> SelectedField<'_, W, F, D> {
    pub fn geometry(&self) -> PolygeroGeometry {
        self.geometry
    }
}

/// A typed list `(SelectedField, Tail)` ending in `()`. This conversion only
/// supplies frontend metadata; all fingerprint arithmetic stays in its sibling.
/// The statement holds every layout (transcript I3), so the list absorbs
/// nothing.
pub trait Fields: Clone {
    type Selection: witness_selection::Fields;
    fn selection(&self) -> Self::Selection;
}
impl Fields for () {
    type Selection = ();
    fn selection(&self) {}
}
impl<'a, const W: usize, F: ZkField<W> + RegisteredField, D: EvaluationDomain<W, F>, T: Fields>
    Fields for (SelectedField<'a, W, F, D>, T)
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
    pub(super) selection: witness_selection::Param<L::Selection>,
}
impl<L: Fields> JointParam<L> {
    pub fn new(fields: L) -> Result<Self, String> {
        Ok(Self {
            selection: witness_selection::Param::new(fields.selection())?,
        })
    }
    pub fn config(&self) -> PolygeroConfig {
        self.selection.config()
    }
}

/// A circuit's packing and commitment layout, independent of the participant list.
/// The statement absorbs it (`CommitmentLayout`) before any prover message.
/// Input packing stays here; the lower-level Polygero participant only knows
/// full-field witness cells and affine constraints over them.
pub struct CircuitParticipant<const W: usize, F: ZkField<W> + PackingField> {
    pub(super) geometry: CircuitGeometry,
    #[cfg(any(test, feature = "prover"))]
    pub(super) config: PolygeroConfig,
    /// The Polygero parameter of the committed cells; `None` for a
    /// participant that commits nothing (pure foreign storage).
    param: Option<PolygeroParam>,
    pub(super) backend: PackingCommitment<F>,
    pub(super) id: [u8; 32],
    pub(super) additional_ids: Vec<[u8; 32]>,
    pub(super) inputs: InputLayout,
    /// Values not all native: the split layout. `None` is all native.
    pub(super) storage: Option<super::storage::Split>,
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
        // Keep the selected field's mask-cell and backend/domain checks even
        // when this circuit will join a larger participant list.
        SelectedField::from_parameter(param.clone(), ctx.domain)?;
        Ok(Self {
            geometry,
            #[cfg(any(test, feature = "prover"))]
            config,
            param: Some(param),
            backend,
            id: circuit.id,
            additional_ids: others.iter().map(|c| c.id).collect(),
            inputs: InputLayout::new(circuits, virtual_inputs)?,
            storage: None,
        })
    }
    /// A single-circuit participant whose values `[private inputs | pads]` are
    /// stored as `storage` says. With some native values (mixed storage), it
    /// commits `[native private inputs | pads | R]` and `mask` holds R's bits
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
        let sc_geom = circuit_geometry(&[circuit])?;
        let inputs = InputLayout::new(&[circuit], 0)?;
        let private = inputs.committed();
        let values = private
            .checked_add(sc_geom.pad_count())
            .ok_or("split layout overflow")?;
        let split = super::storage::Split::new(storage, mask, private, values)?;
        // Mixed storage commits its native values in value order (native
        // private inputs, then pads), then R; pure foreign storage commits
        // nothing and has no Polygero parameter, masks or rows.
        let (committed, pads) = if split.mask.is_some() {
            let pads = sc_geom.pad_count();
            (split.map.native_cells() - pads, pads)
        } else {
            (0, 0)
        };
        let layout = super::packing_commitment::PackingLayout::new(committed, pads, 1)?;
        let param = match split.mask {
            Some(_) => {
                let cells = prepare_parameter(layout.witness_count + 1, config, ctx.domain)?;
                SelectedField::from_parameter(cells.clone(), ctx.domain)?;
                Some(cells)
            }
            None => None,
        };
        let nw = param.as_ref().map_or(0, |p| p.geometry().nw);
        Ok(Self {
            geometry: CircuitGeometry::new(sc_geom, 1, nw).map_err(|e| e.to_string())?,
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
    fn param(&self) -> Result<&PolygeroParam, String> {
        self.param
            .as_ref()
            .ok_or_else(|| "participant commits nothing".into())
    }
    /// The Polygero geometry of this participant's committed cells; an
    /// error if it commits nothing.
    pub(super) fn polygero(&self) -> Result<PolygeroGeometry, String> {
        Ok(self.param()?.geometry())
    }
    /// This participant as a field of the joint commitment. A participant
    /// that commits nothing (pure foreign storage) has none: the call fails.
    pub fn participant<'a, D: EvaluationDomain<W, F>>(
        &'a self,
        ctx: &ZkContext<'a, W, F, D>,
    ) -> Result<SelectedField<'a, W, F, D>, String> {
        SelectedField::from_parameter(self.param()?.clone(), ctx.domain)
    }
}

/// A frontend's statement part: its participant, its circuits (the primary
/// circuit first, as at construction) and the primary circuit's public
/// inputs, checked against each other once. A frontend reads its circuits
/// and public inputs only from here, through its `Bound` (transcript I2).
pub struct FrontendPart<'a, const W: usize, F: ZkField<W> + PackingField> {
    pub(super) participant: &'a CircuitParticipant<W, F>,
    pub(super) circuits: Vec<&'a Circuit<F>>,
    /// The public inputs as elements of the circuit's field.
    pub(super) public: Cow<'a, [F::E]>,
}
impl<'a, const W: usize, F: ZkField<W> + PackingField> FrontendPart<'a, W, F> {
    pub fn new(
        participant: &'a CircuitParticipant<W, F>,
        circuits: &[&'a Circuit<F>],
        public: &'a [CircuitInput<F>],
    ) -> Result<Self, String> {
        participant.validate_circuits(circuits, public.len())?;
        let parameters = &participant.backend.parameters;
        Ok(Self {
            participant,
            circuits: circuits.to_vec(),
            public: parameters
                .extension()
                .input_elements(parameters.field(), public),
        })
    }
}

/// Draw the sumcheck top weights of `t`'s frontend; the statement already
/// holds its circuits and public inputs (transcript I1). The driver draws them where the frontend
/// starts, after the last message the frontend depends on (its virtual-input definitions
/// included), and hands them to `prove`, `prove_split`, `reduce` or
/// `reduce_split` before any other message (transcript I8).
pub fn top_weights<const W: usize, F: ZkField<W> + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, W, F>>,
) -> Result<Challenge<TopWeights<F::E>>, String> {
    let part = t.part();
    let f = part.participant.backend.parameters.field();
    sumcheck::top_weights(&part.circuits, &mut t.transcript(), f)
}

#[cfg(test)]
mod tests;
