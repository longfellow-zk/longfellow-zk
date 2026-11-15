// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The registry of v2 transcript message tags (transcript I6, proto I7).
//!
//! Every message the v2 transcript absorbs starts with one of these tags as a
//! u64. Each tag has one fixed list of values, its schema (`Tag::schema`, an
//! exhaustive table that the encoder's kind codes, the trace checks and the
//! test decoder all read), so the tag alone says how to parse the message;
//! a schema change takes a new tag. Values 0 to 15 are the transcript's node terminators (0: a draw
//! follows, 1: the seal) and are not variants. Ranges group the tags by the
//! component that sends them. `F` is the sending component's field.
//!
//! This file depends on nothing, so the transcript can name `Tag`.

/// The kind of one value of the byte grammar, with its u64 code.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u64)]
pub enum Kind {
    Bytes = 0,
    Nats = 1,
    Elements = 2,
    Bits = 3,
}
impl Kind {
    /// The kind's u64 code on the transcript.
    pub const fn value(self) -> u64 {
        self as u64
    }
}

/// One value of a tag's schema: its kind, and its count where the schema
/// fixes it (`None` where the geometry or the field sets the count).
pub type Value = (Kind, Option<u64>);

/// A v2 transcript message tag. A repeated value fails to compile (E0081).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u64)]
pub enum Tag {
    /// Bytes protocol ID, Bytes session transcript, Bytes(32) combined
    /// hash, Nats(version, attribute count).
    MdocStatement = 16,
    /// Bytes protocol ID, Bytes context.
    ZkStatement = 17,
    /// Bytes(32) circuit ID.
    Circuit = 18,
    /// Nats(FieldID, committed private inputs before packing, pad cells,
    /// fingerprint mask cells), Bytes packing descriptor, Nats(native runs as (first, count,
    /// cell) triples), Nats(bit-stored runs as (first, count, start, width)
    /// quadruples), Nats(mask start, mask width).
    CommitmentLayout = 19,
    /// Nats(k, s, n, t): the proof's one Polygero profile.
    JointGeometry = 20,
    /// Elements(F, n): a circuit's public inputs.
    PublicInputs = 21,
    /// Bytes adapter mode ID, Nats(Q, tree count, virtual leaves per tree),
    /// Nats(quotient pad positions).
    AdapterLayout = 22,
    /// Bytes(32): the joint Merkle root.
    Commitment = 32,
    /// Elements(F, 2): one field's masked fingerprints.
    FingerprintResponse = 33,
    /// Elements(F, 2): c0 - s0, c1 - s1.
    SumcheckRound = 48,
    /// Elements(F, 1): the masked cross coefficient.
    SumcheckCross = 49,
    /// Elements(F, 2): the two masked final claims.
    SumcheckClaims = 50,
    /// Elements(P256, 1): the split message mu.
    SplitOpening = 64,
    /// Bits(Q), Bits(Q): the two masked quotient words.
    P256AdapterQuotients = 65,
    /// Elements(F, m): the trace-zero responses, m the packing degree.
    PackingU = 80,
    /// Elements(F, 1): the trace-zero mask response.
    PackingA = 81,
    /// Elements(F, k + s): H, then Elements(F, 2k): Z.
    PolygeroResponse = 96,
    /// Bytes: every proof byte before the seal block, magic included.
    Seal = 112,
    /// Bytes protocol ID, Bytes context of a standalone packed source.
    SimdStatement = 23,
    /// Bytes(32) source ID, Nats(real source words, committed cells).
    SimdLayout = 24,
    /// Elements(GF128, 1): masked nonlinear residual.
    SimdNonlinear = 130,
    /// Elements(GF128, 128): trace-pairing responses.
    SimdTraceU = 131,
    /// Elements(GF128, 1): trace-pairing mask response.
    SimdTraceA = 132,
    /// Bytes protocol ID, Bytes context, Nats(K,L), Bytes(32) binary ID,
    /// Bytes backend label, Bytes encoded public-key projection matrix.
    MldsaPublicStatement = 25,
    /// Bytes protocol ID, Bytes context, Nats(K,L), Bytes(32) binary ID,
    /// Bytes(32) arithmetic ID, Bytes backend label.
    MldsaHiddenStatement = 26,
    /// Bytes(32) fragment ID, Nats(layer widths).
    MldsaBinaryLayout = 27,
    /// Six Bits(Q) values: exact-mode masked quotient words.
    ExactAdapterQuotients = 192,
    /// Nats(coordinate-map dimensions and storage runs).
    CoordinateLayout = 28,
    /// Nats(affine-coordinate count, signed scales and offsets).
    CoordinateAffine = 29,
    /// Bytes protocol ID, Bytes session, Bytes(32) combined hash,
    /// Nats(version, attribute count).
    SingleCommitmentStatement = 30,
}

impl Tag {
    /// Every tag, in value order, each at its index.
    pub const ALL: [Tag; 30] = [
        Tag::MdocStatement,
        Tag::ZkStatement,
        Tag::Circuit,
        Tag::CommitmentLayout,
        Tag::JointGeometry,
        Tag::PublicInputs,
        Tag::AdapterLayout,
        Tag::SimdStatement,
        Tag::SimdLayout,
        Tag::MldsaPublicStatement,
        Tag::MldsaHiddenStatement,
        Tag::MldsaBinaryLayout,
        Tag::CoordinateLayout,
        Tag::CoordinateAffine,
        Tag::SingleCommitmentStatement,
        Tag::Commitment,
        Tag::FingerprintResponse,
        Tag::SumcheckRound,
        Tag::SumcheckCross,
        Tag::SumcheckClaims,
        Tag::SplitOpening,
        Tag::P256AdapterQuotients,
        Tag::PackingU,
        Tag::PackingA,
        Tag::PolygeroResponse,
        Tag::Seal,
        Tag::SimdNonlinear,
        Tag::SimdTraceU,
        Tag::SimdTraceA,
        Tag::ExactAdapterQuotients,
    ];
    /// The tag's u64 value on the transcript.
    pub const fn value(self) -> u64 {
        self as u64
    }
    /// The tag's position in `ALL`. The match is exhaustive, so a new tag
    /// does not compile until it has a position, and the registry test
    /// checks that `ALL` holds every tag at its position.
    pub const fn index(self) -> usize {
        match self {
            Tag::MdocStatement => 0,
            Tag::ZkStatement => 1,
            Tag::Circuit => 2,
            Tag::CommitmentLayout => 3,
            Tag::JointGeometry => 4,
            Tag::PublicInputs => 5,
            Tag::AdapterLayout => 6,
            Tag::SimdStatement => 7,
            Tag::SimdLayout => 8,
            Tag::MldsaPublicStatement => 9,
            Tag::MldsaHiddenStatement => 10,
            Tag::MldsaBinaryLayout => 11,
            Tag::CoordinateLayout => 12,
            Tag::CoordinateAffine => 13,
            Tag::SingleCommitmentStatement => 14,
            Tag::Commitment => 15,
            Tag::FingerprintResponse => 16,
            Tag::SumcheckRound => 17,
            Tag::SumcheckCross => 18,
            Tag::SumcheckClaims => 19,
            Tag::SplitOpening => 20,
            Tag::P256AdapterQuotients => 21,
            Tag::PackingU => 22,
            Tag::PackingA => 23,
            Tag::PolygeroResponse => 24,
            Tag::Seal => 25,
            Tag::SimdNonlinear => 26,
            Tag::SimdTraceU => 27,
            Tag::SimdTraceA => 28,
            Tag::ExactAdapterQuotients => 29,
        }
    }
    /// Whether the tag is a setup message's, which only the statement
    /// writes, before every prover message (transcript I1, I3). The match is
    /// exhaustive, so a new tag must say which it is.
    pub const fn is_setup(self) -> bool {
        match self {
            Tag::MdocStatement
            | Tag::ZkStatement
            | Tag::Circuit
            | Tag::CommitmentLayout
            | Tag::JointGeometry
            | Tag::PublicInputs
            | Tag::AdapterLayout
            | Tag::SimdStatement
            | Tag::SimdLayout
            | Tag::MldsaPublicStatement
            | Tag::MldsaHiddenStatement
            | Tag::MldsaBinaryLayout
            | Tag::CoordinateLayout
            | Tag::CoordinateAffine
            | Tag::SingleCommitmentStatement => true,
            Tag::Commitment
            | Tag::FingerprintResponse
            | Tag::SumcheckRound
            | Tag::SumcheckCross
            | Tag::SumcheckClaims
            | Tag::SplitOpening
            | Tag::P256AdapterQuotients
            | Tag::PackingU
            | Tag::PackingA
            | Tag::PolygeroResponse
            | Tag::Seal
            | Tag::SimdNonlinear
            | Tag::SimdTraceU
            | Tag::SimdTraceA
            | Tag::ExactAdapterQuotients => false,
        }
    }
    /// The tag with value `value`, if any.
    pub fn from_value(value: u64) -> Option<Tag> {
        Self::ALL.into_iter().find(|t| t.value() == value)
    }
    /// The tag's schema, the one list of values every message with this
    /// tag writes, in order (transcript I6). The match is exhaustive, so a
    /// new tag cannot be added without its schema.
    pub const fn schema(self) -> &'static [Value] {
        use Kind::{Bits, Bytes, Elements, Nats};
        match self {
            Tag::MdocStatement => &[
                (Bytes, None),
                (Bytes, None),
                (Bytes, Some(32)),
                (Nats, Some(2)),
            ],
            Tag::ZkStatement => &[(Bytes, None), (Bytes, None)],
            Tag::Circuit => &[(Bytes, Some(32))],
            Tag::CommitmentLayout => &[
                (Nats, Some(4)),
                (Bytes, None),
                (Nats, None),
                (Nats, None),
                (Nats, Some(2)),
            ],
            Tag::JointGeometry => &[(Nats, Some(4))],
            Tag::PublicInputs => &[(Elements, None)],
            Tag::AdapterLayout => &[(Bytes, None), (Nats, Some(3)), (Nats, None)],
            Tag::Commitment => &[(Bytes, Some(32))],
            Tag::FingerprintResponse => &[(Elements, Some(2))],
            Tag::SumcheckRound => &[(Elements, Some(2))],
            Tag::SumcheckCross => &[(Elements, Some(1))],
            Tag::SumcheckClaims => &[(Elements, Some(2))],
            Tag::SplitOpening => &[(Elements, Some(1))],
            Tag::P256AdapterQuotients => &[(Bits, None), (Bits, None)],
            Tag::PackingU => &[(Elements, None)],
            Tag::PackingA => &[(Elements, Some(1))],
            Tag::PolygeroResponse => &[(Elements, None), (Elements, None)],
            Tag::Seal => &[(Bytes, None)],
            Tag::SimdStatement => &[(Bytes, None), (Bytes, None)],
            Tag::SimdLayout | Tag::MldsaBinaryLayout => &[(Bytes, Some(32)), (Nats, None)],
            Tag::SimdNonlinear | Tag::SimdTraceA => &[(Elements, Some(1))],
            Tag::SimdTraceU => &[(Elements, Some(128))],
            Tag::MldsaPublicStatement => &[
                (Bytes, None),
                (Bytes, None),
                (Nats, Some(2)),
                (Bytes, Some(32)),
                (Bytes, None),
                (Bytes, None),
            ],
            Tag::MldsaHiddenStatement => &[
                (Bytes, None),
                (Bytes, None),
                (Nats, Some(2)),
                (Bytes, Some(32)),
                (Bytes, Some(32)),
                (Bytes, None),
            ],
            Tag::ExactAdapterQuotients => &[
                (Bits, None),
                (Bits, None),
                (Bits, None),
                (Bits, None),
                (Bits, None),
                (Bits, None),
            ],
            Tag::CoordinateLayout | Tag::CoordinateAffine => &[(Nats, None)],
            Tag::SingleCommitmentStatement => &[
                (Bytes, None),
                (Bytes, None),
                (Bytes, Some(32)),
                (Nats, Some(2)),
            ],
        }
    }
    /// Whether one message's values, as (kind code, count) pairs in order,
    /// follow this tag's schema.
    pub fn admits(self, values: &[(u64, u64)]) -> bool {
        let schema = self.schema();
        values.len() == schema.len()
            && values
                .iter()
                .zip(schema)
                .all(|(&(kind, count), &(want, fixed))| {
                    kind == want.value() && fixed.is_none_or(|n| n == count)
                })
    }
}

#[cfg(test)]
mod tests;
