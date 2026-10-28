// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared v2 proof envelope and deterministic commitment layout.
use crate::{
    core::{
        algebra::{ElementOf, SerializableField},
        proto::circuit::Circuit,
    },
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            RuntimeField,
        },
        proto::{
            dual_packing::PackingProof,
            polygero::{
                PolygeroCommitment, PolygeroGeometry, PolygeroProductConstraint, PolygeroProof,
            },
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
    pub fn suffix_count(&self) -> usize {
        self.pad_cells
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProofGeometry {
    pub sc_geom: SumcheckProofGeometry,
    pub com_geom: PolygeroGeometry,
    pub packing_degree: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProof<const W: usize, F: SerializableField> {
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub com: PolygeroCommitment,
    pub packing: PackingProof<ElementOf<F>>,
    pub com_proof: PolygeroProof<ElementOf<F>>,
}
impl<const W: usize, F: RuntimeField<W> + SerializableField> ZkProof<W, F> {
    pub fn write_to_buf(
        &self,
        buf: &mut Vec<u8>,
        g: &ZkProofGeometry,
        f: &F,
    ) -> std::io::Result<()> {
        use std::io::{Error, ErrorKind};
        match &self.packing {
            PackingProof::Direct if g.packing_degree == 1 => {}
            PackingProof::TraceZero { u, .. }
                if g.packing_degree > 1 && u.len() == g.packing_degree => {}
            _ => return Err(Error::new(ErrorKind::InvalidData, "v2 packing shape")),
        }
        buf.extend_from_slice(b"LFV4");
        buf.extend_from_slice(&self.com.root.data);
        self.sumcheck_proof.write_to_buf(buf, &g.sc_geom, f)?;
        if let PackingProof::TraceZero { u, a } = &self.packing {
            for x in u.iter().chain(std::iter::once(a)) {
                super::util::write_elt_field(buf, x, f);
            }
        }
        self.com_proof.write_to_buf(buf, &g.com_geom, f)
    }
    pub fn write(&self, g: &ZkProofGeometry, f: &F) -> std::io::Result<Vec<u8>> {
        let mut b = Vec::new();
        self.write_to_buf(&mut b, g, f)?;
        Ok(b)
    }
    pub fn read(b: &mut &[u8], g: &ZkProofGeometry, f: &F) -> std::io::Result<Self> {
        use std::io::{Error, ErrorKind};
        if b.get(..4) != Some(b"LFV4") {
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
        let com_proof = super::polygero::read(b, &g.com_geom, f)?;
        Ok(Self {
            sumcheck_proof,
            com,
            packing,
            com_proof,
        })
    }
}
pub fn packing_layout<F: SerializableField + PackingField>(
    c: &Circuit<F>,
    f: &F,
) -> Result<
    (
        PackingLayout,
        SumcheckProofGeometry,
        Vec<PolygeroProductConstraint>,
    ),
    String,
> {
    packing_layout_with_degree(c, f.packing_extension().degree())
}
pub fn packing_layout_with_degree<F: SerializableField>(
    c: &Circuit<F>,
    degree: usize,
) -> Result<
    (
        PackingLayout,
        SumcheckProofGeometry,
        Vec<PolygeroProductConstraint>,
    ),
    String,
> {
    c.validate_v2()?;
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
    let products = product_constraints(layout.suffix_start, &sc);
    Ok((layout, sc, products))
}
pub fn commitment_layout<F: SerializableField + PackingField>(
    c: &Circuit<F>,
    f: &F,
) -> (SumcheckProofGeometry, usize, Vec<PolygeroProductConstraint>) {
    let (l, s, p) = packing_layout(c, f).expect("valid commitment layout");
    (s, l.witness_count, p)
}
pub(crate) fn product_constraints(
    start: usize,
    g: &SumcheckProofGeometry,
) -> Vec<PolygeroProductConstraint> {
    g.claim_indices(start)
        .map(|[x, y, z]| PolygeroProductConstraint { x, y, z })
        .collect()
}
pub fn witness_and_constraint_count<F: SerializableField + PackingField>(
    c: &Circuit<F>,
    f: &F,
) -> (usize, usize) {
    let (_, nw, p) = commitment_layout(c, f);
    (nw, p.len())
}
