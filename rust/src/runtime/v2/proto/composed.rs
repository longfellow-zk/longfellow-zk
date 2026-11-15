// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The body of a composed proof: a binary host participant and one mixed
//! split participant, opened jointly. Applications wrap it in their own
//! envelope (version and final seal).
//!
//! Fields are encoded in send order (proto I4): the shared root, both
//! fields' fingerprint responses, the split sumcheck, the split message
//! `mu`, the adapter's message, the host sumcheck and packing, both
//! Polygero responses; then the terminal section: both fields' opened rows,
//! the nonces and the frontier, which is the rest of the body.
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::{
        algebra::RuntimeField,
        v2::proto::{
            polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig},
            sumcheck::SumcheckProof,
            witness_selection::{FingerprintResponse, FINGERPRINTS},
            zk::{CircuitGeometry, CircuitProof},
            Digest,
        },
    },
};

/// The adapter's message in a composed proof, with its canonical encoding
/// of exactly `BYTES` bytes.
pub trait AdapterMessage: Sized {
    const BYTES: usize;
    fn write(&self, out: &mut Vec<u8>);
    fn read(b: &mut &[u8]) -> Result<Self, String>;
}

/// Public dimensions of a composed proof: the host and split circuit
/// geometries and the proof's one Polygero profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedGeometry {
    pub host: CircuitGeometry,
    pub split: CircuitGeometry,
    pub config: PolygeroConfig,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedProof<
    const WH: usize,
    H: SerializableField,
    const WS: usize,
    S: SerializableField,
    M,
> {
    pub commitment: PolygeroCommitment,
    pub fingerprints: (
        FingerprintResponse<ElementOf<H>>,
        (FingerprintResponse<ElementOf<S>>, ()),
    ),
    /// The split frontend's sumcheck; split storage has packing degree one.
    pub split: SumcheckProof<WS, S>,
    /// The split message `mu`.
    pub mu: ElementOf<S>,
    /// The adapter's message.
    pub message: M,
    pub host: CircuitProof<WH, H>,
    pub polygero: JointPolygeroProof<(FieldProof<ElementOf<H>>, (FieldProof<ElementOf<S>>, ()))>,
}
impl<
        const WH: usize,
        H: RuntimeField<WH> + SerializableField,
        const WS: usize,
        S: RuntimeField<WS> + SerializableField,
        M: AdapterMessage,
    > ComposedProof<WH, H, WS, S, M>
{
    /// Bytes of every body field but the frontier (proto I3); None if they
    /// overflow.
    pub fn fixed_len(g: &ComposedGeometry, h: &H, s: &S) -> Option<usize> {
        let (wh, ws) = (h.serialized_size_bytes(), s.serialized_size_bytes());
        let [host_response, host_rows] = FieldProof::<()>::wire_lengths(&g.host.com_geom, wh)?;
        let [split_response, split_rows] = FieldProof::<()>::wire_lengths(&g.split.com_geom, ws)?;
        if g.split.packing_degree != 1 {
            return None;
        }
        [
            Some(32),
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
    pub fn write_to_buf(
        &self,
        out: &mut Vec<u8>,
        g: &ComposedGeometry,
        h: &H,
        s: &S,
    ) -> Result<(), String> {
        out.extend_from_slice(&self.commitment.root.data);
        self.fingerprints.0.write(out, h);
        self.fingerprints.1 .0.write(out, s);
        self.split
            .write_to_buf(out, &g.split.sc_geom, s)
            .map_err(|e| e.to_string())?;
        out.extend_from_slice(&s.to_bytes(&self.mu));
        self.message.write(out);
        self.host
            .write_to_buf(out, &g.host, h)
            .map_err(|e| e.to_string())?;
        let (gh, gs) = (&g.host.com_geom, &g.split.com_geom);
        self.polygero
            .write_to_buf::<std::io::Error>(
                out,
                g.config.t,
                g.config.n,
                |b, buf| {
                    b.0.write_response(buf, gh, h)?;
                    b.1 .0.write_response(buf, gs, s)
                },
                |b, buf| {
                    b.0.write_rows(buf, gh, h)?;
                    b.1 .0.write_rows(buf, gs, s)
                },
            )
            .map_err(|e| e.to_string())
    }
    /// Read exactly the whole body `b`, whose length the complete reader has
    /// checked against `fixed_len` (proto I3): the frontier is its rest.
    pub fn read(body: &[u8], g: &ComposedGeometry, h: &H, s: &S) -> Result<Self, String> {
        let mut rest = body;
        let b = &mut rest;
        let commitment = PolygeroCommitment {
            root: Digest {
                data: super::util::read_bytes_32(b).map_err(|e| e.to_string())?,
            },
        };
        let fingerprints = (
            FingerprintResponse::read(b, h).map_err(|e| e.to_string())?,
            (
                FingerprintResponse::read(b, s).map_err(|e| e.to_string())?,
                (),
            ),
        );
        let split = SumcheckProof::read(b, &g.split.sc_geom, s).map_err(|e| e.to_string())?;
        let mu = super::read_field(b, s).map_err(|e| e.to_string())?;
        let message = M::read(b)?;
        let host = CircuitProof::read(b, &g.host, h).map_err(|e| e.to_string())?;
        let (gh, gs) = (&g.host.com_geom, &g.split.com_geom);
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
