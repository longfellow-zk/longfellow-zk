// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Longfellow v2 zk proof types and wire encoding.

use std::io::Result;

use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::{
        algebra::field::RuntimeField,
        proto::{
            polygero::{
                PolygeroCommitment, PolygeroGeometry, PolygeroProductConstraint, PolygeroProof,
            },
            sumcheck_v2::{SumcheckProof, SumcheckProofGeometry},
        },
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProofGeometry {
    pub sc_geom: SumcheckProofGeometry,
    pub com_geom: PolygeroGeometry,
}

/// A complete Zero-Knowledge proof.
///
/// Contains the sumcheck proof, commitment root,
/// and the Polygero proof over the constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProof<const W: usize, F: SerializableField> {
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub com: PolygeroCommitment,
    pub com_proof: PolygeroProof<ElementOf<F>>,
}

impl<const W: usize, F: RuntimeField<W> + SerializableField> ZkProof<W, F> {
    pub fn write_to_buf(&self, buf: &mut Vec<u8>, geom: &ZkProofGeometry, f: &F) -> Result<()> {
        buf.extend_from_slice(b"LFV2");
        buf.extend_from_slice(&self.com.root.data);
        self.sumcheck_proof.write_to_buf(buf, &geom.sc_geom, f)?;
        self.com_proof.write_to_buf(buf, &geom.com_geom, f)?;
        Ok(())
    }

    pub fn write(&self, geom: &ZkProofGeometry, f: &F) -> Result<Vec<u8>> {
        let mut buf = Vec::new();
        self.write_to_buf(&mut buf, geom, f)?;
        Ok(buf)
    }

    pub fn read(bytes: &mut &[u8], geom: &ZkProofGeometry, f: &F) -> Result<Self> {
        if bytes.get(..4) != Some(b"LFV2") {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Longfellow v2 version marker",
            ));
        }
        *bytes = &bytes[4..];
        let root_bytes = crate::runtime::proto::util::read_bytes_32(bytes)?;
        let com = PolygeroCommitment {
            root: crate::runtime::proto::Digest { data: root_bytes },
        };

        let sumcheck_proof = SumcheckProof::read(bytes, &geom.sc_geom, f)?;
        let com_proof = crate::runtime::proto::polygero::read(bytes, &geom.com_geom, f)?;

        Ok(ZkProof {
            sumcheck_proof,
            com,
            com_proof,
        })
    }
}

/// Derive public commitment metadata from the trusted circuit. Compilation uses
/// it to choose dimensions; both runtime roles use it to prepare those dimensions.
/// Private inputs precede all layer pads. Each layer's last three pad positions
/// contain p_A, p_B and p_A*p_B, fixing one product constraint before challenges.
pub fn commitment_layout<F: SerializableField>(
    circuit: &crate::core::proto::v2::Circuit<F>,
) -> (SumcheckProofGeometry, usize, Vec<PolygeroProductConstraint>) {
    let (nw, _) = witness_and_constraint_count(circuit);
    let sumcheck = SumcheckProofGeometry::from_circuit(circuit);
    let nprivate = circuit.raw.ninput - circuit.raw.npublic_input;
    let products = product_constraints(nprivate, &sumcheck);
    (sumcheck, nw, products)
}

/// Coordinates of the final-claim pads and their product, in layer order.
pub(crate) fn product_constraints(
    start_pad: usize,
    geometry: &SumcheckProofGeometry,
) -> Vec<PolygeroProductConstraint> {
    geometry
        .claim_indices(start_pad)
        .map(|[x, y, z]| PolygeroProductConstraint { x, y, z })
        .collect()
}

/// Count committed witnesses and pad-product constraints. Linear constraints
/// are compiled later and have a separate count (one more than the layer count).
#[must_use]
pub fn witness_and_constraint_count<F: SerializableField>(
    circuit: &crate::core::proto::v2::Circuit<F>,
) -> (usize, usize) {
    assert!(
        circuit.raw.ninput >= circuit.raw.npublic_input,
        "npublic_input ({}) exceeds ninput ({})",
        circuit.raw.npublic_input,
        circuit.raw.ninput
    );

    let n_witness = circuit.raw.ninput - circuit.raw.npublic_input;
    let mut pad_witness_len = 0;
    for clr in &circuit.raw.layers {
        assert!(
            crate::core::proto::sane_logw(clr.logw()),
            "logw must be sane"
        );
        pad_witness_len += crate::runtime::proto::sumcheck_v2::pad_count(clr.logw());
    }
    let nw = n_witness + pad_witness_len;
    let nq = circuit.raw.layers.len();
    (nw, nq)
}
