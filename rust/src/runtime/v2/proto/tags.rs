// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The registry of v2 transcript message tags (transcript I6, proto I7).
//!
//! Every message the v2 transcript absorbs starts with one of these tags as a
//! u64. Each tag has one fixed list of value kinds, written next to it, so
//! the tag alone says how to parse the message; a schema change takes a new
//! tag. Values 0 to 15 are the transcript's node terminators (0: a draw
//! follows, 1: the seal) and are not variants. Ranges group the tags by the
//! component that sends them. `F` is the sending component's field.
//!
//! This file depends on nothing, so the transcript can name `Tag`.

/// A v2 transcript message tag. A repeated value fails to compile (E0081).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u64)]
pub enum Tag {
    /// Bytes protocol ID, Bytes session transcript, Bytes(32) combined
    /// hash, Nats(version, attribute count).
    MdocStatement = 16,
    /// Bytes protocol ID, Bytes context.
    ZkStatement = 17,
    /// Bytes(32) circuit ID, Nats(nw of each layer), Nats(output count,
    /// input count, public input count).
    Circuit = 18,
    /// Nats(FieldID, committed private cells, pad cells, fingerprint mask
    /// cells), Bytes packing descriptor, Nats(storage runs), Nats(mask
    /// start, mask width).
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
}

impl Tag {
    /// The tag's u64 value on the transcript.
    pub const fn value(self) -> u64 {
        self as u64
    }
}
