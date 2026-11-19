// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The body of a composed proof: a binary host participant and one mixed
//! split participant, opened jointly. Applications wrap it in their own
//! envelope (version and final seal).
//!
//! Fields are encoded in send order (proto I4): the shared root, both
//! fields' fingerprint responses, the split sumcheck, the split message
//! `mu`, the adapter's message, the host sumcheck and packing, both
//! Polygero responses; then the terminal section: both fields' opened rows,
//! the nonces and the frontier, its u64 count first.
#[cfg(feature = "testonly")]
use crate::core::algebra::SerializableField;

mod geometry;
pub use geometry::ComposedGeometry;

cfg_role! {
    mod body;
    pub(crate) use body::{AdapterMessage, ComposedProof};
}
cfg_prover! {
    mod prover;
    pub(crate) use prover::WriteAdapterMessage;
}
cfg_verifier! {
    mod verifier;
    pub(crate) use verifier::ReadAdapterMessage;
}

/// Serialized sizes of the parts of a composed body, in bytes, for the
/// benchmarks' size report.
#[cfg(feature = "testonly")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BodySizes {
    /// The host circuit's reduction: its sumcheck and packing.
    pub host: usize,
    /// The split frontend's sumcheck.
    pub split: usize,
    /// The host field's Polygero responses and opened rows.
    pub host_payload: usize,
    /// The split field's Polygero responses and opened rows.
    pub split_payload: usize,
    /// The Merkle nonces.
    pub nonces: usize,
    /// The Merkle frontier, its count included.
    pub frontier: usize,
    /// The adapter's message.
    pub message: usize,
}
#[cfg(feature = "testonly")]
#[cfg_attr(not(feature = "mdoc"), allow(dead_code))]
impl<H: SerializableField, S: SerializableField, M: AdapterMessage> ComposedProof<H, S, M> {
    /// The sizes of this body's parts under `g`.
    pub(crate) fn sizes(&self, g: &ComposedGeometry, h: &H, s: &S) -> Result<BodySizes, String> {
        let mut host = Vec::new();
        self.host
            .write_to_buf(&mut host, &g.host, h)
            .map_err(|e| e.to_string())?;
        let split = self
            .split
            .write(g.split.sumcheck(), s)
            .map_err(|e| e.to_string())?;
        let (nonces, frontier) = self.polygero.authentication_bytes();
        let bodies = self.polygero.bodies();
        Ok(BodySizes {
            host: host.len(),
            split: split.len(),
            host_payload: bodies.0.payload_bytes(h),
            split_payload: bodies.1 .0.payload_bytes(s),
            nonces,
            frontier,
            message: M::BYTES,
        })
    }
}

#[cfg(test)]
mod tests;
