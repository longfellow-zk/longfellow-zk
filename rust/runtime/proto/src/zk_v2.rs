// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared v2 proof envelope and deterministic commitment layout.
use crate::{
    core::{
        algebra::{ElementOf, SerializableField},
        proto::v2::Circuit,
    },
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            RuntimeField,
        },
        proto::{
            dual_packing::PackingProof,
            polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroGeometry},
            sumcheck_v2::{SumcheckProof, SumcheckProofGeometry},
        },
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackingLayout {
    pub private_inputs: usize,
    pub packed_words: usize,
    pub masks: usize,
    pub suffix_start: usize,
    pub pad_cells: usize,
    pub witness_count: usize,
    pub degree: usize,
}
impl PackingLayout {
    pub fn new(private_inputs: usize, pad_cells: usize, degree: usize) -> Result<Self, String> {
        if degree == 0 {
            return Err("zero packing degree".into());
        }
        let packed_words = private_inputs.div_ceil(degree);
        let masks = if degree == 1 {
            0
        } else {
            degree.checked_add(1).ok_or("packing layout overflow")?
        };
        let suffix_start = packed_words
            .checked_add(masks)
            .ok_or("packing layout overflow")?;
        let witness_count = suffix_start
            .checked_add(pad_cells)
            .ok_or("packing layout overflow")?;
        Ok(Self {
            private_inputs,
            packed_words,
            masks,
            suffix_start,
            pad_cells,
            witness_count,
            degree,
        })
    }
}
/// Circuit reduction dimensions, independent of its enclosing participant list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitGeometry {
    pub sc_geom: SumcheckProofGeometry,
    pub com_geom: PolygeroGeometry,
    pub packing_degree: usize,
}
/// Complete standalone proof geometry, including its selected joint commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProofGeometry {
    pub circuit: CircuitGeometry,
    pub joint_context: super::Digest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProof<const W: usize, F: SerializableField> {
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub com: PolygeroCommitment,
    pub fingerprints: super::witness_selection::FingerprintResponse<ElementOf<F>>,
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
            let raw = b
                .get(..size)
                .ok_or_else(|| Error::new(ErrorKind::UnexpectedEof, "packing response"))?;
            let mut v = raw
                .chunks_exact(width)
                .map(|x| {
                    let e = f
                        .bytes_to_element(x)
                        .map_err(|e| Error::new(ErrorKind::InvalidData, e))?;
                    if f.to_bytes(&e) != x {
                        return Err(Error::new(
                            ErrorKind::InvalidData,
                            "noncanonical packing response",
                        ));
                    }
                    Ok(e)
                })
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
impl<const W: usize, F: RuntimeField<W> + SerializableField> ZkProof<W, F> {
    fn write_body(&self, buf: &mut Vec<u8>, g: &ZkProofGeometry, f: &F) -> std::io::Result<()> {
        buf.extend_from_slice(b"LFV9");
        buf.extend_from_slice(&self.com.root.data);
        self.fingerprints.write(buf, f);
        CircuitProof::<W, F>::write_parts(&self.sumcheck_proof, &self.packing, buf, &g.circuit, f)?;
        self.com_proof.write_to_buf(
            buf,
            &g.joint_context,
            g.circuit.com_geom.t,
            g.circuit.com_geom.n,
            |b, out| b.0.write(out, &g.circuit.com_geom, f),
        )
    }
    pub fn write(
        &self,
        g: &ZkProofGeometry,
        f: &F,
        transcript: crate::runtime::random::transcript_v2::Transcript,
    ) -> std::io::Result<crate::runtime::random::transcript_v2::EncodedProof> {
        let mut b = Vec::new();
        self.write_body(&mut b, g, f)?;
        Ok(transcript.append_final_seal(b))
    }
    pub fn read<'a>(
        b: &mut &'a [u8],
        g: &ZkProofGeometry,
        f: &F,
    ) -> std::io::Result<crate::runtime::random::transcript_v2::Unverified<'a, Self>> {
        let input = *b;
        use std::io::{Error, ErrorKind};
        if b.get(..4) != Some(b"LFV9") {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Longfellow v2 version marker",
            ));
        }
        *b = &b[4..];
        let com = PolygeroCommitment {
            root: super::Digest {
                data: super::util::read_bytes_32(b)?,
            },
        };
        let fingerprints = super::witness_selection::FingerprintResponse::read(b, f)?;
        let CircuitProof {
            sumcheck_proof,
            packing,
        } = CircuitProof::read(b, &g.circuit, f)?;
        let com_proof = JointPolygeroProof::read::<std::io::Error>(
            b,
            &g.joint_context,
            g.circuit.com_geom.t,
            g.circuit.com_geom.n,
            |b| Ok((FieldProof::read(b, &g.circuit.com_geom, f)?, ())),
        )?;
        let body = Self {
            sumcheck_proof,
            com,
            fingerprints,
            packing,
            com_proof,
        };
        crate::runtime::random::transcript_v2::Unverified::decoded(body, input, b)
    }
}
pub fn packing_layout<F: SerializableField + PackingField>(
    c: &Circuit<F>,
    f: &F,
) -> Result<(PackingLayout, SumcheckProofGeometry), String> {
    packing_layout_with_degree(c, f.packing_extension().degree())
}
pub fn packing_layout_with_degree<F: SerializableField>(
    c: &Circuit<F>,
    degree: usize,
) -> Result<(PackingLayout, SumcheckProofGeometry), String> {
    let sc = SumcheckProofGeometry::from_circuit(c);
    sc.serialized_elements().map_err(|e| e.to_string())?;
    let pads = sc.logw_layers.iter().try_fold(0usize, |n, &l| {
        n.checked_add(super::sumcheck_v2::pad_count(l))
            .ok_or("packing layout overflow")
    })?;
    let layout = PackingLayout::new(
        c.raw
            .ninput
            .checked_sub(c.raw.npublic_input)
            .ok_or("public prefix")?,
        pads,
        degree,
    )?;
    Ok((layout, sc))
}
pub fn commitment_layout<F: SerializableField + PackingField>(
    c: &Circuit<F>,
    f: &F,
) -> (SumcheckProofGeometry, usize) {
    let (layout, geometry) = packing_layout(c, f).expect("valid commitment layout");
    (
        geometry,
        layout
            .witness_count
            .checked_add(super::witness_selection::FINGERPRINTS)
            .expect("valid selected commitment layout"),
    )
}
