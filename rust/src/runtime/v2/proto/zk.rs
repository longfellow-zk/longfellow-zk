// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 proof messages, public geometry and complete-proof encoding.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::v2::{
    proto::{polygero::checked_body, witness_selection::FINGERPRINTS},
    transcript::{Bound, Unverified, SEAL_BYTES},
};
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::{
        algebra::RuntimeField,
        v2::{
            proto::{
                dual_packing::PackingProof,
                polygero::{
                    FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig,
                    PolygeroGeometry,
                },
                sumcheck::{SumcheckProof, SumcheckProofGeometry},
            },
            transcript::{EncodedProof, Transcript},
        },
    },
};

/// Circuit reduction dimensions, independent of its enclosing participant list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitGeometry {
    pub sc_geom: SumcheckProofGeometry,
    pub com_geom: PolygeroGeometry,
    pub packing_degree: usize,
}
/// Complete standalone proof geometry: one circuit and the proof's one
/// Polygero profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProofGeometry {
    pub circuit: CircuitGeometry,
    pub config: PolygeroConfig,
}
/// A standalone proof; its fields are in send order (proto I4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProof<const W: usize, F: SerializableField> {
    pub com: PolygeroCommitment,
    pub fingerprints: super::witness_selection::FingerprintResponse<ElementOf<F>>,
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub packing: PackingProof<ElementOf<F>>,
    pub com_proof: JointPolygeroProof<(FieldProof<ElementOf<F>>, ())>,
}
/// A circuit reduction, authenticated later by its participant's shared opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitProof<const W: usize, F: SerializableField> {
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub packing: PackingProof<ElementOf<F>>,
}
impl<const W: usize, F: RuntimeField<W> + SerializableField> CircuitProof<W, F> {
    fn write_parts(
        sumcheck: &SumcheckProof<W, F>,
        packing: &PackingProof<F::E>,
        buf: &mut Vec<u8>,
        g: &CircuitGeometry,
        f: &F,
    ) -> std::io::Result<()> {
        use std::io::{Error, ErrorKind};
        match packing {
            PackingProof::Direct if g.packing_degree == 1 => {}
            PackingProof::TraceZero { u, .. }
                if g.packing_degree > 1 && u.len() == g.packing_degree => {}
            _ => return Err(Error::new(ErrorKind::InvalidData, "v2 packing shape")),
        }
        sumcheck.write_to_buf(buf, &g.sc_geom, f)?;
        if let PackingProof::TraceZero { u, a } = packing {
            for x in u.iter().chain(std::iter::once(a)) {
                super::util::write_elt_field(buf, x, f);
            }
        }
        Ok(())
    }
    pub fn write_to_buf(
        &self,
        buf: &mut Vec<u8>,
        g: &CircuitGeometry,
        f: &F,
    ) -> std::io::Result<()> {
        Self::write_parts(&self.sumcheck_proof, &self.packing, buf, g, f)
    }
    pub fn write(&self, g: &CircuitGeometry, f: &F) -> std::io::Result<Vec<u8>> {
        let mut out = Vec::new();
        self.write_to_buf(&mut out, g, f)?;
        Ok(out)
    }
    pub fn read(b: &mut &[u8], g: &CircuitGeometry, f: &F) -> std::io::Result<Self> {
        use std::io::{Error, ErrorKind};
        let sumcheck_proof = SumcheckProof::read(b, &g.sc_geom, f)?;
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
            if g.packing_degree == 0 || width == 0 {
                return Err(Error::new(ErrorKind::InvalidData, "packing geometry"));
            }
            let mut raw = b
                .get(..size)
                .ok_or_else(|| Error::new(ErrorKind::UnexpectedEof, "packing response"))?;
            let mut v = (0..count)
                .map(|_| super::read_field(&mut raw, f))
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
impl CircuitGeometry {
    /// Bytes of a circuit proof: the sumcheck, then packing U and A when the
    /// packing degree exceeds one; None if they overflow.
    pub(crate) fn proof_len(&self, width: usize) -> Option<usize> {
        let elements = self.sc_geom.serialized_elements().ok()?;
        let packing = match self.packing_degree {
            0 => return None,
            1 => 0,
            m => m.checked_add(1)?,
        };
        elements.checked_add(packing)?.checked_mul(width)
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl ZkProofGeometry {
    /// Bytes of every body field before the frontier and its count: root, fingerprints,
    /// circuit proof, response, rows and nonces (proto I3).
    fn fixed_len(&self, width: usize) -> Option<usize> {
        let g = &self.circuit.com_geom;
        let [response, rows] = FieldProof::<()>::wire_lengths(g, width)?;
        [
            Some(32),
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
    pub const MAGIC: [u8; 4] = *b"LFV9";
    /// `LFV9`, then the body in send order: root, fingerprints, sumcheck,
    /// packing, response; then the terminal rows, nonces and frontier (its
    /// count, then its digests).
    fn write_body(&self, buf: &mut Vec<u8>, g: &ZkProofGeometry, f: &F) -> std::io::Result<()> {
        buf.extend_from_slice(&Self::MAGIC);
        buf.extend_from_slice(&self.com.root.data);
        self.fingerprints.write(buf, f);
        CircuitProof::<W, F>::write_parts(&self.sumcheck_proof, &self.packing, buf, &g.circuit, f)?;
        let geom = &g.circuit.com_geom;
        self.com_proof.write_to_buf(
            buf,
            g.config.t,
            g.config.n,
            |b, out| b.0.write_response(out, geom, f),
            |b, out| b.0.write_rows(out, geom, f),
        )
    }
    pub fn write(
        &self,
        g: &ZkProofGeometry,
        f: &F,
        transcript: Transcript,
    ) -> std::io::Result<EncodedProof> {
        let mut b = Vec::new();
        self.write_body(&mut b, g, f)?;
        Ok(transcript.append_final_seal(b))
    }
    /// Parse one complete proof against the absorbed geometry (proto I2).
    /// The total length is checked before anything is decoded (proto I3).
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
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
            root: super::Digest {
                data: super::util::read_bytes_32(&mut b)?,
            },
        };
        let fingerprints = super::witness_selection::FingerprintResponse::read(&mut b, f)?;
        let CircuitProof {
            sumcheck_proof,
            packing,
        } = CircuitProof::read(&mut b, &geometry.circuit, f)?;
        let geom = &geometry.circuit.com_geom;
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
