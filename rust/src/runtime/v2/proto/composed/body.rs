// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The composed proof body and its length, which every proof role uses.
use super::{
    super::{
        merkle::DIGEST_LEN,
        polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment},
        sumcheck::SumcheckProof,
        witness_selection::{FingerprintResponse, FINGERPRINTS},
        zk::CircuitProof,
    },
    ComposedGeometry,
};
use crate::core::algebra::{ElementOf, SerializableField};

/// The adapter's message in a composed proof, with its canonical encoding
/// of exactly `BYTES` bytes: the prover writes it (`WriteAdapterMessage`),
/// the verifier reads it (`ReadAdapterMessage`).
#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
pub(crate) trait AdapterMessage: Sized {
    const BYTES: usize;
}

/// A composed proof body. Only an application's complete reader, which
/// checks the length and the seal, parses one (proto I2).
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
pub(crate) struct ComposedProof<H: SerializableField, S: SerializableField, M> {
    pub(crate) commitment: PolygeroCommitment,
    pub(crate) fingerprints: (
        FingerprintResponse<ElementOf<H>>,
        (FingerprintResponse<ElementOf<S>>, ()),
    ),
    /// The split frontend's sumcheck; split storage has packing degree one.
    pub(crate) split: SumcheckProof<S>,
    /// The split message `mu`.
    pub(crate) mu: ElementOf<S>,
    /// The adapter's message.
    pub(crate) message: M,
    pub(crate) host: CircuitProof<H>,
    pub(crate) polygero:
        JointPolygeroProof<(FieldProof<ElementOf<H>>, (FieldProof<ElementOf<S>>, ()))>,
}
/// A bare body, for tests that authenticate one without an application's
/// envelope.
#[cfg(test)]
impl<H: SerializableField, S: SerializableField, M> AsRef<Self> for ComposedProof<H, S, M> {
    fn as_ref(&self) -> &Self {
        self
    }
}
#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
impl<H: SerializableField, S: SerializableField, M: AdapterMessage> ComposedProof<H, S, M> {
    /// Bytes of every body field before the frontier and its count (proto
    /// I3); None if they overflow.
    pub(crate) fn fixed_len(g: &ComposedGeometry, h: &H, s: &S) -> Option<usize> {
        let (wh, ws) = (h.serialized_size_bytes(), s.serialized_size_bytes());
        let [gh, gs] = g.polygero();
        let [host_response, host_rows] = FieldProof::<()>::wire_lengths(&gh, wh)?;
        let [split_response, split_rows] = FieldProof::<()>::wire_lengths(&gs, ws)?;
        [
            Some(DIGEST_LEN),
            FINGERPRINTS.checked_mul(wh),
            FINGERPRINTS.checked_mul(ws),
            g.split.proof_len(ws),
            Some(ws),
            Some(M::BYTES),
            g.host.proof_len(wh),
            Some(host_response),
            Some(split_response),
            Some(host_rows),
            Some(split_rows),
            JointPolygeroProof::<()>::fixed_opening_len(g.config.t),
        ]
        .into_iter()
        .try_fold(0usize, |total, x| total.checked_add(x?))
    }
}
