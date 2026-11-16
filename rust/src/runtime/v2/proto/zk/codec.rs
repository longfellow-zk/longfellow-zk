// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The decoding of v2 proofs and their length checks, which every proof role
//! runs; the encoding is the prover's (`prover.rs`).
use super::{
    super::{
        merkle::DIGEST_LEN,
        polygero::codec::checked_body,
        read_bytes_32, read_field,
        witness_selection::{FingerprintResponse, FINGERPRINTS},
        Digest,
    },
    CircuitProof, CircuitProofGeometry, FieldProof, JointPolygeroProof, PackingProof,
    PolygeroCommitment, SumcheckProof, ZkProof, ZkProofGeometry,
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::RuntimeField,
        v2::transcript::{Bound, Unverified, SEAL_BYTES},
    },
};

impl<const W: usize, F: RuntimeField<W> + SerializableField> CircuitProof<W, F> {
    /// A component reader, called only by the complete readers (proto I2).
    pub(crate) fn read(b: &mut &[u8], g: &CircuitProofGeometry, f: &F) -> std::io::Result<Self> {
        use std::io::{Error, ErrorKind};
        let sumcheck_proof = SumcheckProof::read(b, &g.sumcheck, f)?;
        let packing = if g.packing_degree == 1 {
            PackingProof::Direct
        } else {
            let count = g
                .packing_degree
                .checked_add(1)
                .ok_or_else(|| Error::new(ErrorKind::InvalidData, "packing geometry"))?;
            let width = f.serialized_size_bytes();
            let size = count
                .checked_mul(width)
                .ok_or_else(|| Error::new(ErrorKind::InvalidData, "packing geometry"))?;
            if width == 0 {
                return Err(Error::new(ErrorKind::InvalidData, "packing geometry"));
            }
            let mut raw = b
                .get(..size)
                .ok_or_else(|| Error::new(ErrorKind::UnexpectedEof, "packing response"))?;
            let mut v = (0..count)
                .map(|_| read_field(&mut raw, f))
                .collect::<std::io::Result<Vec<_>>>()?;
            *b = &b[size..];
            let a = v.pop().unwrap();
            PackingProof::TraceZero { u: v, a }
        };
        Ok(Self {
            sumcheck_proof,
            packing,
        })
    }
}
impl CircuitProofGeometry {
    /// Bytes of a circuit proof: the sumcheck, then packing U and A when the
    /// packing degree exceeds one; None if they overflow.
    pub(crate) fn proof_len(&self, width: usize) -> Option<usize> {
        let elements = self.sumcheck.serialized_elements();
        let packing = match self.packing_degree {
            1 => 0,
            m => m.checked_add(1)?,
        };
        elements.checked_add(packing)?.checked_mul(width)
    }
}
impl ZkProofGeometry {
    /// Bytes of every body field before the frontier and its count: root, fingerprints,
    /// circuit proof, response, rows and nonces (proto I3).
    fn fixed_len(&self, width: usize) -> Option<usize> {
        let [response, rows] = FieldProof::<()>::wire_lengths(&self.polygero(), width)?;
        [
            Some(DIGEST_LEN),
            FINGERPRINTS.checked_mul(width),
            self.circuit.proof_len(width),
            Some(response),
            Some(rows),
            JointPolygeroProof::<()>::fixed_opening_len(self.config.t),
        ]
        .into_iter()
        .try_fold(0usize, |total, x| total.checked_add(x?))
    }
}
impl<const W: usize, F: RuntimeField<W> + SerializableField> ZkProof<W, F> {
    /// Parse one complete proof against the absorbed geometry (proto I2).
    /// The total length is checked before anything is decoded (proto I3).
    pub fn read<'a>(
        bytes: &'a [u8],
        g: &Bound<'_, ZkProofGeometry>,
        f: &F,
    ) -> std::io::Result<Unverified<'a, Self>> {
        use std::io::{Error, ErrorKind};
        let geometry = g.part();
        let fixed = geometry
            .fixed_len(f.serialized_size_bytes())
            .ok_or_else(|| Error::new(ErrorKind::InvalidData, "proof geometry"))?;
        let (t, n) = (geometry.config.t, geometry.config.n);
        let mut b = checked_body(bytes, Self::MAGIC.len(), fixed, t, n)?;
        if bytes[..4] != Self::MAGIC {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Longfellow v2 version marker",
            ));
        }
        let com = PolygeroCommitment {
            root: Digest {
                data: read_bytes_32(&mut b)?,
            },
        };
        let fingerprints = FingerprintResponse::read(&mut b, f)?;
        let CircuitProof {
            sumcheck_proof,
            packing,
        } = CircuitProof::read(&mut b, &geometry.circuit, f)?;
        let geom = &geometry.polygero();
        let com_proof = JointPolygeroProof::read::<std::io::Error>(
            &mut b,
            t,
            n,
            |r| Ok((FieldProof::read_response(r, geom, f)?, ())),
            |bodies, r| bodies.0.read_rows(r, geom, f),
        )?;
        let body = Self {
            com,
            fingerprints,
            sumcheck_proof,
            packing,
            com_proof,
        };
        let mut seal = &bytes[bytes.len() - SEAL_BYTES..];
        Unverified::decoded(body, bytes, &mut seal)
    }
}
