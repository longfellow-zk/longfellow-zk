// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The v2 statement messages of a frontend: its circuits, its commitment
//! layout and its public inputs, and the joint geometry (transcript I1, I3).
//! They are setup messages: only a statement writes them, once, before any
//! prover message. Sumcheck, packing and witness selection send their own
//! messages after it.
use super::{
    joint::{CircuitParticipant, FrontendPart},
    storage::{Group, Run},
};
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{packing::PackingField, ZkField},
        v2::{
            proto::{
                polygero::PolygeroConfig, tags::Tag, witness_selection::FINGERPRINTS,
                zk::ZkProofGeometry,
            },
            transcript::{Encoder, Header, Message, SetupMessage, Statement, ZkStatement},
        },
    },
};

/// `Circuit` (18): Bytes(32) circuit ID; Nats(nw of each layer, outputs to
/// inputs, as stored); Nats(output count, input count, public input count).
/// The sumcheck schedule derives each stage's logw from the layer widths.
struct CircuitMessage<'a, F: SerializableField>(&'a Circuit<F>);
impl<F: SerializableField> Message for CircuitMessage<'_, F> {
    const TAG: Tag = Tag::Circuit;
    fn encode(&self, e: &mut Encoder<'_>) {
        let raw = &self.0.raw;
        e.bytes(&self.0.id);
        let widths: Vec<u64> = raw.layers.iter().map(|l| l.nw as u64).collect();
        e.nats(&widths);
        e.nats(&[
            raw.noutput as u64,
            raw.ninput as u64,
            raw.npublic_input as u64,
        ]);
    }
}
impl<F: SerializableField> SetupMessage for CircuitMessage<'_, F> {}

/// `CommitmentLayout` (19), one per field participant:
///
/// - Nats(FieldID, committed private inputs, pad cells, fingerprint mask cells). The private inputs
///   are the logical (unpacked) inputs the field commits: all private inputs of a native
///   participant, the native ones of a split participant. A participant that commits nothing (pure
///   foreign storage) has zeros.
/// - Bytes: the packing descriptor (field, embedding, degree and basis).
/// - Nats: the storage runs of a split participant, flattened as `0, first value, count, first
///   cell` for a native run and `1, first value, count, first bit, bits per value` for a run of
///   values stored as bits of the binary commitment; empty for a native participant.
/// - Nats(mask start, mask width): the bits of the split mask R among the binary inputs (its native
///   cell follows every native value); (0, 0) without one.
///
/// The packing masks follow from the descriptor's degree, and the
/// committed cell count `nw` from all of these.
struct LayoutMessage<'a, const W: usize, F: ZkField<W> + PackingField>(
    &'a CircuitParticipant<W, F>,
);
impl<const W: usize, F: ZkField<W> + PackingField> Message for LayoutMessage<'_, W, F> {
    const TAG: Tag = Tag::CommitmentLayout;
    fn encode(&self, e: &mut Encoder<'_>) {
        let p = self.0;
        let f = p.backend.parameters.field();
        let layout = &p.backend.layout;
        let (private, pads, masks) = if p.commits() {
            (layout.private_inputs, layout.pad_cells, FINGERPRINTS)
        } else {
            (0, 0, 0)
        };
        e.nats(&[
            f.field_id() as u64,
            private as u64,
            pads as u64,
            masks as u64,
        ]);
        e.bytes(&p.backend.parameters.descriptor());
        let mut runs = Vec::new();
        let mut mask = Group::EMPTY;
        if let Some(split) = &p.storage {
            for run in split.map.runs() {
                match run {
                    Run::Native { first, count, cell } => runs.extend([0, first, count, cell]),
                    Run::Prime {
                        first,
                        count,
                        start,
                        width,
                    } => runs.extend([1, first, count, start, width]),
                }
            }
            mask = split.mask.unwrap_or(Group::EMPTY);
        }
        let flat: Vec<u64> = runs.into_iter().map(|x| x as u64).collect();
        e.nats(&flat);
        e.nats(&[mask.start() as u64, mask.width() as u64]);
    }
}
impl<const W: usize, F: ZkField<W> + PackingField> SetupMessage for LayoutMessage<'_, W, F> {}

/// `JointGeometry` (20): Nats(k, s, n, t), the one Polygero profile of the
/// proof. It is the only place the statement holds the profile; each
/// field's committed cell count follows from its `CommitmentLayout`.
struct JointGeometryMessage(PolygeroConfig);
impl Message for JointGeometryMessage {
    const TAG: Tag = Tag::JointGeometry;
    fn encode(&self, e: &mut Encoder<'_>) {
        let c = self.0;
        e.nats(&[c.k as u64, c.s as u64, c.n as u64, c.t as u64]);
    }
}
impl SetupMessage for JointGeometryMessage {}

/// `PublicInputs` (21): Elements(F, npublic), a primary circuit's public
/// inputs as elements of its field, the representation the circuit reads.
struct PublicInputsMessage<'a, F: SerializableField> {
    f: &'a F,
    inputs: &'a [F::E],
}
impl<F: SerializableField> Message for PublicInputsMessage<'_, F> {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, self.inputs);
    }
}
impl<F: SerializableField> SetupMessage for PublicInputsMessage<'_, F> {}

impl<const W: usize, F: ZkField<W> + PackingField> FrontendPart<'_, W, F> {
    /// One `Circuit` message per circuit of this frontend, primary first.
    pub fn write_circuits(&self, h: &mut Header<'_>) {
        for c in &self.circuits {
            h.send(&CircuitMessage(*c));
        }
    }
    /// This frontend's `CommitmentLayout`.
    pub fn write_layout(&self, h: &mut Header<'_>) {
        h.send(&LayoutMessage(self.participant));
    }
    /// This frontend's `PublicInputs`.
    pub fn write_public(&self, h: &mut Header<'_>) {
        h.send(&PublicInputsMessage {
            f: self.participant.backend.parameters.field(),
            inputs: &self.public,
        });
    }
}

/// The `JointGeometry` of a proof: its one Polygero profile, the `config`
/// of the geometry its proof is parsed and verified against.
pub fn write_joint_geometry(h: &mut Header<'_>, config: PolygeroConfig) {
    h.send(&JointGeometryMessage(config));
}

/// The statement of a standalone ZK proof: `ZkStatement` (protocol ID,
/// context), then the frontend's `Circuit` messages, its
/// `CommitmentLayout`, the `JointGeometry` and its `PublicInputs`. The proof
/// is parsed against `geometry`, the geometry it writes (transcript I2).
pub struct ZkProofStatement<'a, const W: usize, F: ZkField<W> + PackingField> {
    pub(super) context: &'a [u8],
    pub(super) part: FrontendPart<'a, W, F>,
    pub(super) geometry: ZkProofGeometry,
}
impl<'a, const W: usize, F: ZkField<W> + PackingField> ZkProofStatement<'a, W, F> {
    pub fn part(&self) -> &FrontendPart<'a, W, F> {
        &self.part
    }
    pub fn geometry(&self) -> &ZkProofGeometry {
        &self.geometry
    }
}
impl<const W: usize, F: ZkField<W> + PackingField> Statement for ZkProofStatement<'_, W, F> {
    fn write(&self, h: &mut Header<'_>) {
        h.send(&ZkStatement {
            context: self.context,
        });
        self.part.write_circuits(h);
        self.part.write_layout(h);
        write_joint_geometry(h, self.geometry.config);
        self.part.write_public(h);
    }
}
