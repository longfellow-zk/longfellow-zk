// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The v2 statement messages of a frontend: its circuits, its commitment
//! layout and its public inputs, and the joint geometry (transcript I1, I3).
//! They are setup messages: only a statement writes them, once, before any
//! prover message. Sumcheck, packing and witness selection send their own
//! messages after it.
use super::{
    joint::{CircuitParticipant, FrontendPart},
    storage::{Group, Run},
    CircuitInput,
};
use crate::{
    core::{
        algebra::{RegisteredField, SerializableField},
        proto::v2::Circuit,
    },
    runtime::{
        algebra::{packing::PackingField, ZkField},
        v2::{
            proto::{
                polygero::PolygeroConfig, tags::Tag, witness_selection::FINGERPRINTS,
                zk::ZkProofGeometry,
            },
            transcript::{
                Bound, Encoder, Header, Message, Opened, SetupMessage, Statement, ZkStatement,
            },
        },
    },
};

/// `Circuit` (18): Bytes(32) circuit ID. The ID hashes the whole circuit,
/// its field and its shape included (output, input and public input counts,
/// each layer's width), so the statement holds those values once, through
/// the ID; the sumcheck schedule derives each stage's logw from the
/// circuit the ID names.
struct CircuitMessage<'a, F: SerializableField>(&'a Circuit<F>);
impl<F: SerializableField> Message for CircuitMessage<'_, F> {
    const TAG: Tag = Tag::Circuit;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(&self.0.id);
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
/// - Nats: the native storage runs of a split participant, consecutive `(first value, count, first
///   cell)` triples.
/// - Nats: its runs of values stored as bits of the binary commitment, consecutive `(first value,
///   count, first bit, bits per value)` quadruples.
///
///   Each list is in increasing first value; a native participant writes two empty lists.
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
        let (mut native, mut stored) = (Vec::new(), Vec::new());
        let mut mask = Group::EMPTY;
        if let Some(split) = &p.storage {
            // `runs` is in value order, so each list is in increasing first value.
            for run in split.map.runs() {
                match run {
                    Run::Native { first, count, cell } => {
                        native.extend([first, count, cell].map(|x| x as u64))
                    }
                    Run::Prime {
                        first,
                        count,
                        start,
                        width,
                    } => stored.extend([first, count, start, width].map(|x| x as u64)),
                }
            }
            mask = split.mask.unwrap_or(Group::EMPTY);
        }
        e.nats(&native);
        e.nats(&stored);
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
struct PublicInputsMessage<'a, F: RegisteredField> {
    f: &'a F,
    inputs: &'a [F::E],
}
impl<F: RegisteredField> Message for PublicInputsMessage<'_, F> {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.f, self.inputs);
    }
}
impl<F: RegisteredField> SetupMessage for PublicInputsMessage<'_, F> {}

impl<const W: usize, F: ZkField<W> + PackingField> FrontendPart<'_, W, F> {
    /// One `Circuit` message per circuit of this frontend, primary first.
    pub fn write_circuits(&self, h: &mut Header<'_>) {
        for c in self.circuits() {
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
pub(crate) fn write_joint_geometry(h: &mut Header<'_>, config: PolygeroConfig) {
    h.send(&JointGeometryMessage(config));
}

/// The statement of a standalone ZK proof: `ZkStatement` (protocol ID,
/// context), then the frontend's `Circuit` messages, its
/// `CommitmentLayout`, the `JointGeometry` and its `PublicInputs`. The proof
/// is parsed against `geometry`, the geometry it writes (transcript I2).
pub struct ZkProofStatement<'a, const W: usize, F: ZkField<W> + PackingField> {
    pub(super) identity: ZkStatement<'a>,
    pub(super) part: FrontendPart<'a, W, F>,
    pub(super) geometry: ZkProofGeometry,
}
impl<'a, const W: usize, F: ZkField<W> + PackingField> ZkProofStatement<'a, W, F> {
    /// The statement of a proof of `circuit`, the one circuit of
    /// `participant`, on `public` under `context`. Both standalone roles
    /// build their statements here.
    pub(super) fn new(
        context: &'a [u8],
        participant: &'a CircuitParticipant<W, F>,
        circuit: &'a Circuit<F>,
        public: &'a [CircuitInput<F>],
    ) -> Result<Self, String> {
        let profile = participant.polygero()?.config();
        Ok(Self {
            identity: ZkStatement { context },
            part: FrontendPart::new(participant, &[circuit], public)?,
            geometry: ZkProofGeometry::new(participant.geometry(), profile)
                .map_err(|e| e.to_string())?,
        })
    }
}
impl<'s, 'a: 's, const W: usize, F: ZkField<W> + PackingField>
    Opened<'s, ZkProofStatement<'a, W, F>>
{
    /// The session, bound to the geometry its statement wrote, which the
    /// proof is parsed against (`ZkProof::read`, transcript I2).
    pub fn geometry(&mut self) -> Bound<'_, ZkProofGeometry> {
        self.bound(|s| &s.geometry)
    }
}
impl<'a, const W: usize, F: ZkField<W> + PackingField> Statement for ZkProofStatement<'a, W, F> {
    type Identity = ZkStatement<'a>;
    fn identity(&self) -> &ZkStatement<'a> {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        self.part.write_circuits(h);
        self.part.write_layout(h);
        write_joint_geometry(h, self.geometry.config());
        self.part.write_public(h);
    }
}
