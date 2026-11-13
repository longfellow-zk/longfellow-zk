// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The body of a composed proof: a binary host participant and one mixed
//! split participant, opened jointly. Applications wrap it in their own
//! envelope (version and final seal).
//!
//! Fields are encoded in protocol order: the shared root, both fields'
//! fingerprint responses, the split message `mu`, the adapter's message, the
//! host and split reductions, then the joint opening.
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::{
        algebra::RuntimeField,
        v2::proto::{
            polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig},
            witness_selection::FingerprintResponse,
            zk::{CircuitGeometry, CircuitProof},
            Digest,
        },
    },
};

/// The adapter's message in a composed proof, with its canonical encoding.
pub trait AdapterMessage: Sized {
    fn write(&self, out: &mut Vec<u8>);
    fn read(b: &mut &[u8]) -> Result<Self, String>;
}

/// Public dimensions of a composed proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedGeometry {
    pub host: CircuitGeometry,
    pub split: CircuitGeometry,
    pub joint_context: Digest,
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
    /// The split message `mu`.
    pub mu: ElementOf<S>,
    /// The adapter's message.
    pub message: M,
    pub host: CircuitProof<WH, H>,
    pub split: CircuitProof<WS, S>,
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
        out.extend_from_slice(&s.to_bytes(&self.mu));
        self.message.write(out);
        self.host
            .write_to_buf(out, &g.host, h)
            .map_err(|e| e.to_string())?;
        self.split
            .write_to_buf(out, &g.split, s)
            .map_err(|e| e.to_string())?;
        self.polygero
            .write_to_buf::<std::io::Error>(
                out,
                &g.joint_context,
                g.config.t,
                g.config.n,
                |b, out| {
                    b.0.write(out, &g.host.com_geom, h)?;
                    b.1 .0.write(out, &g.split.com_geom, s)
                },
            )
            .map_err(|e| e.to_string())
    }
    pub fn read(b: &mut &[u8], g: &ComposedGeometry, h: &H, s: &S) -> Result<Self, String> {
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
        let mu = super::read_field(b, s).map_err(|e| e.to_string())?;
        let message = M::read(b)?;
        let host = CircuitProof::read(b, &g.host, h).map_err(|e| e.to_string())?;
        let split = CircuitProof::read(b, &g.split, s).map_err(|e| e.to_string())?;
        let polygero = JointPolygeroProof::read::<std::io::Error>(
            b,
            &g.joint_context,
            g.config.t,
            g.config.n,
            |b| {
                Ok((
                    FieldProof::read(b, &g.host.com_geom, h)?,
                    (FieldProof::read(b, &g.split.com_geom, s)?, ()),
                ))
            },
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            commitment,
            fingerprints,
            mu,
            message,
            host,
            split,
            polygero,
        })
    }
}
