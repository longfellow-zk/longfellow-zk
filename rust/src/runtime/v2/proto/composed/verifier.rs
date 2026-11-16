// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's decoding of a composed proof body.
use super::{
    super::{
        polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment},
        read_bytes_32, read_field,
        sumcheck::SumcheckProof,
        witness_selection::FingerprintResponse,
        zk::CircuitProof,
        Digest,
    },
    AdapterMessage, ComposedGeometry, ComposedProof,
};
use crate::core::algebra::SerializableField;

/// An adapter message the verifier reads: exactly `BYTES` bytes. Only the
/// crate's complete readers call `read`, after the whole proof's length check
/// (proto I2).
#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
pub(crate) trait ReadAdapterMessage: AdapterMessage {
    fn read(b: &mut &[u8]) -> Result<Self, String>;
}

#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
impl<H: SerializableField, S: SerializableField, M: ReadAdapterMessage> ComposedProof<H, S, M> {
    /// Read exactly the whole body `b`, whose length the complete reader has
    /// checked against `fixed_len` (proto I3): the frontier is its rest.
    /// Crate-private: only an application's complete reader, which checks the
    /// length and the seal, calls it (proto I2).
    pub(crate) fn read(body: &[u8], g: &ComposedGeometry, h: &H, s: &S) -> Result<Self, String> {
        let mut rest = body;
        let b = &mut rest;
        let commitment = PolygeroCommitment {
            root: Digest {
                data: read_bytes_32(b).map_err(|e| e.to_string())?,
            },
        };
        let fingerprints = (
            FingerprintResponse::read(b, h).map_err(|e| e.to_string())?,
            (
                FingerprintResponse::read(b, s).map_err(|e| e.to_string())?,
                (),
            ),
        );
        let split = SumcheckProof::read(b, g.split.sumcheck(), s).map_err(|e| e.to_string())?;
        let mu = read_field(b, s).map_err(|e| e.to_string())?;
        let message = M::read(b)?;
        let host = CircuitProof::read(b, &g.host, h).map_err(|e| e.to_string())?;
        let [gh, gs] = &g.polygero();
        let polygero = JointPolygeroProof::read::<std::io::Error>(
            b,
            g.config.t,
            g.config.n,
            |r| {
                Ok((
                    FieldProof::read_response(r, gh, h)?,
                    (FieldProof::read_response(r, gs, s)?, ()),
                ))
            },
            |bodies, r| {
                bodies.0.read_rows(r, gh, h)?;
                bodies.1 .0.read_rows(r, gs, s)
            },
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            commitment,
            fingerprints,
            split,
            mu,
            message,
            host,
            polygero,
        })
    }
}
