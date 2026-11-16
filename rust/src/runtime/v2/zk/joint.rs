// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Selected joint commitments and circuit metadata for v2 composition.
use std::borrow::Cow;

#[cfg(test)]
use super::storage::StorageMap;
use super::{
    context::{prepare_circuit_layout, CircuitInput},
    packing_commitment::PackingCommitment,
    storage::MixedStorage,
    InputLayout,
};
use crate::{
    core::{
        algebra::{FieldID, RegisteredField},
        proto::v2::Circuit,
    },
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
                zk::CircuitProofGeometry,
            },
            witness_selection::{self, Field, Fields},
        },
    },
};

/// Zk-v2 owns the composition: receipt and commitment select the witness before
/// any frontend challenge, and completion necessarily authenticates those rows.
///
/// `L` is the joint field list, a `(witness_selection::Field, Tail)` list
/// ending in `()`; each field's fingerprint arithmetic stays in witness
/// selection.
#[derive(Clone)]
pub(crate) struct JointParam<L: Fields> {
    pub(super) selection: witness_selection::Param<L>,
}
impl<L: Fields> JointParam<L> {
    pub(crate) fn new(fields: L) -> Result<Self, String> {
        Ok(Self {
            selection: witness_selection::Param::new(fields)?,
        })
    }
    pub(crate) fn config(&self) -> PolygeroConfig {
        self.selection.config()
    }
}

/// A participant's field must be registered (`RegisteredField`), never
/// `FieldID::None`, and this value of it must be the field its ID names: the
/// transcript identifies the field by `F::ID` alone.
pub(super) fn check_registered<F: RegisteredField>(f: &F) -> Result<(), String> {
    if F::ID == FieldID::None || f.field_id() != F::ID || f.serialized_size_bytes() != F::BYTES {
        return Err("v2 participant field is not registered".into());
    }
    Ok(())
}

/// What every participant has, whatever its storage: its circuits' IDs, its
/// proof geometry, its profile, its shared input layout and its field's
/// packing and commitment layout. The statement absorbs it
/// (`CommitmentLayout`) before any prover message. Input packing stays
/// here; the lower-level Polygero participant only knows full-field witness
/// cells and affine constraints over them.
pub(crate) struct Frontend<F: ZkField + PackingField> {
    pub(super) geometry: CircuitProofGeometry,
    #[cfg(any(test, feature = "prover"))]
    pub(super) config: PolygeroConfig,
    pub(super) backend: PackingCommitment<F>,
    pub(super) id: [u8; 32],
    pub(super) additional_ids: Vec<[u8; 32]>,
    pub(super) inputs: InputLayout,
}
impl<F: ZkField + PackingField> Frontend<F> {
    /// Check that `circuits` are this frontend's circuits, in order, and
    /// that `public` inputs fit the primary circuit.
    fn validate_circuits(&self, circuits: &[&Circuit<F>], public: usize) -> Result<(), String> {
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
    /// The field of this frontend's circuits and commitment, the field of
    /// the domain its participant was built with.
    pub(crate) fn field(&self) -> &F {
        self.backend.parameters.field()
    }
}

/// A participant with all its values native: a circuit list whose private
/// inputs, sumcheck pads and packing masks it commits itself.
pub struct CircuitParticipant<F: ZkField + PackingField> {
    pub(super) frontend: Frontend<F>,
    /// The Polygero parameter of the committed cells.
    param: PolygeroParam,
}
impl<F: ZkField + PackingField> CircuitParticipant<F> {
    /// Prove `circuits` as one layered sumcheck; `circuits[0]` is the primary
    /// circuit. They share the public prefix and read prefixes of one input
    /// array. Each intermediate layer has one wire array; only the sparse quad
    /// terms retain their local indexing.
    ///
    /// The last `virtual_inputs` entries of the shared input array are virtual:
    /// each proof defines them as affine functions of committed inputs (see
    /// `VirtualInputs`). The primary circuit cannot read them; the other
    /// components may.
    pub fn new<D: EvaluationDomain<F>>(
        circuits: &[&Circuit<F>],
        virtual_inputs: usize,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, String> {
        check_registered(domain.field())?;
        let (circuit, others) = circuits.split_first().ok_or("empty circuit list")?;
        let (geometry, param, backend, inputs) = prepare_circuit_layout(
            circuits,
            virtual_inputs,
            config,
            domain.field().packing_extension(),
            domain,
        )?;
        // Keep the selected field's mask-cell and backend/domain checks even
        // when this circuit will join a larger participant list.
        Field::new(param.clone(), domain)?;
        Ok(Self {
            frontend: Frontend {
                geometry,
                #[cfg(any(test, feature = "prover"))]
                config,
                backend,
                id: circuit.id,
                additional_ids: others.iter().map(|c| c.id).collect(),
                inputs,
            },
            param,
        })
    }
    pub fn geometry(&self) -> CircuitProofGeometry {
        self.frontend.geometry.clone()
    }
    /// The field of this participant's circuits and commitment, the field of
    /// the domain it was built with.
    pub(crate) fn field(&self) -> &F {
        self.frontend.field()
    }
    /// The Polygero geometry of this participant's committed cells.
    pub(super) fn polygero(&self) -> PolygeroGeometry {
        self.param.geometry()
    }
    /// This participant as a field of the joint commitment, over `domain`,
    /// the domain it was built with.
    pub(crate) fn participant<'a, D: EvaluationDomain<F>>(
        &'a self,
        domain: &'a D,
    ) -> Result<Field<'a, F, D>, String> {
        Field::new(self.param.clone(), domain)
    }
}

/// How a participant stores its values `[private inputs | pads]`, as its
/// statement's `CommitmentLayout` describes them.
pub(crate) enum StorageLayout<'a> {
    /// Every value in the participant's own commitment.
    Native,
    /// Some values as bit groups of the binary commitment, the rest and R in
    /// the participant's own commitment (`split::MixedSplit`).
    Mixed(&'a MixedStorage),
    /// Every value as a bit group of the binary commitment; the participant
    /// commits nothing (`split::PureSplit`, tests only until a driver uses it).
    #[cfg(test)]
    Pure(&'a StorageMap),
}

/// A participant of one storage mode: native (`CircuitParticipant`), mixed
/// (`split::MixedSplit`) or pure foreign (`split::PureSplit`). The frontend
/// steps that every mode shares read its `Frontend`; the statement writes
/// every mode alike from its `Frontend` and its `StorageLayout`.
pub(crate) trait Participant<F: ZkField + PackingField> {
    fn frontend(&self) -> &Frontend<F>;
    fn storage(&self) -> StorageLayout<'_>;
    /// The Polygero parameter of the committed cells, if it commits any.
    #[cfg(test)]
    fn param_for_test(&self) -> Option<&PolygeroParam>;
}
impl<F: ZkField + PackingField> Participant<F> for CircuitParticipant<F> {
    fn frontend(&self) -> &Frontend<F> {
        &self.frontend
    }
    fn storage(&self) -> StorageLayout<'_> {
        StorageLayout::Native
    }
    #[cfg(test)]
    fn param_for_test(&self) -> Option<&PolygeroParam> {
        Some(&self.param)
    }
}

/// A frontend's statement part: its participant, its circuits (the primary
/// circuit first, as at construction) and the primary circuit's public
/// inputs, checked against each other once. A frontend reads its circuits
/// and public inputs only from here, through its `Bound` (transcript I2).
/// `P` is the participant's storage mode, so a step for one mode takes
/// only that mode's parts.
pub(crate) struct FrontendPart<'a, F: ZkField + PackingField, P = CircuitParticipant<F>> {
    pub(super) participant: &'a P,
    circuits: Vec<&'a Circuit<F>>,
    /// The public inputs as elements of the circuit's field.
    pub(super) public: Cow<'a, [F::E]>,
}
impl<'a, F: ZkField + PackingField, P: Participant<F>> FrontendPart<'a, F, P> {
    pub(crate) fn new(
        participant: &'a P,
        circuits: &[&'a Circuit<F>],
        public: &'a [CircuitInput<F>],
    ) -> Result<Self, String> {
        let frontend = participant.frontend();
        frontend.validate_circuits(circuits, public.len())?;
        let parameters = &frontend.backend.parameters;
        Ok(Self {
            participant,
            circuits: circuits.to_vec(),
            public: parameters
                .extension()
                .input_elements(parameters.field(), public),
        })
    }
    /// The participant's frontend: what every storage mode shares.
    pub(crate) fn frontend(&self) -> &'a Frontend<F> {
        self.participant.frontend()
    }
    /// The circuits of this frontend, primary first.
    pub(super) fn circuits(&self) -> &[&'a Circuit<F>] {
        &self.circuits
    }
    /// The field of this frontend, its participant's: the one field the
    /// frontend's steps compute in.
    pub(crate) fn field(&self) -> &'a F {
        self.frontend().field()
    }
}

#[cfg(test)]
pub(crate) mod tests;
