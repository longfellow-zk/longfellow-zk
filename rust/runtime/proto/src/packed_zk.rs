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

//! Experimental packed GF128 proof envelope. Direct-field LFV2 is unchanged.
use crate::{
    core::proto::circuit::Circuit,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128, Gf2_128Field},
            Subfield,
        },
        proto::{
            polygero::{PolygeroCommitment, PolygeroProductConstraint, PolygeroProof},
            ring_switch::{RingSwitch128Proof, RING_MASK_CELLS},
            sumcheck_v2::{SumcheckProof, SumcheckProofGeometry},
            zk_v2::{product_constraints, ZkProofGeometry},
        },
    },
};
/// Physical committed positions. Only GKR's final pads introduce products.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedLayout {
    pub private_bits: usize,
    pub packed_words: usize,
    pub caller_auxiliary: usize,
    pub ring_start: usize,
    pub gkr_start: usize,
    pub witness_count: usize,
}
impl PackedLayout {
    pub fn new(
        circuit: &Circuit<Gf2_128Field>,
        auxiliary: usize,
    ) -> Result<(Self, SumcheckProofGeometry, Vec<PolygeroProductConstraint>), String> {
        let bits = circuit
            .raw
            .ninput
            .checked_sub(circuit.raw.npublic_input)
            .ok_or("invalid public prefix")?;
        let packed_words = bits.div_ceil(128);
        let ring_start = packed_words
            .checked_add(auxiliary)
            .ok_or("packed layout overflow")?;
        let gkr_start = ring_start
            .checked_add(RING_MASK_CELLS)
            .ok_or("packed layout overflow")?;
        let sc = SumcheckProofGeometry::from_circuit(circuit);
        sc.serialized_elements().map_err(|e| e.to_string())?;
        let pads = sc.logw_layers.iter().try_fold(0usize, |n, &logw| {
            n.checked_add(crate::runtime::proto::sumcheck_v2::pad_count(logw))
                .ok_or("packed layout overflow")
        })?;
        let witness_count = gkr_start
            .checked_add(pads)
            .ok_or("packed layout overflow")?;
        let products = product_constraints(gkr_start, &sc);
        Ok((
            Self {
                private_bits: bits,
                packed_words,
                caller_auxiliary: auxiliary,
                ring_start,
                gkr_start,
                witness_count,
            },
            sc,
            products,
        ))
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedZkProof {
    pub sumcheck_proof: SumcheckProof<2, Gf2_128Field>,
    pub ring_proof: RingSwitch128Proof,
    pub com: PolygeroCommitment,
    pub com_proof: PolygeroProof<Gf2_128>,
}
impl PackedZkProof {
    pub fn write<SF: Subfield<E = Gf2_128>>(
        &self,
        geom: &ZkProofGeometry,
        f: &Gf2_128Field,
        sf: &SF,
    ) -> std::io::Result<Vec<u8>> {
        let mut out = Vec::new();
        self.write_to_buf(&mut out, geom, f, sf)?;
        Ok(out)
    }
    pub fn write_to_buf<SF: Subfield<E = Gf2_128>>(
        &self,
        out: &mut Vec<u8>,
        geom: &ZkProofGeometry,
        f: &Gf2_128Field,
        sf: &SF,
    ) -> std::io::Result<()> {
        out.extend_from_slice(b"LFB2");
        out.extend_from_slice(&self.com.root.data);
        self.sumcheck_proof.write_to_buf(out, &geom.sc_geom, f)?;
        self.ring_proof.write_to_buf(out);
        self.com_proof.write_to_buf(out, &geom.com_geom, f, sf)
    }
    pub fn read<SF: Subfield<E = Gf2_128>>(
        bytes: &mut &[u8],
        geom: &ZkProofGeometry,
        f: &Gf2_128Field,
        sf: &SF,
    ) -> std::io::Result<Self> {
        if bytes.get(..4) != Some(b"LFB2") {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "packed proof marker",
            ));
        }
        *bytes = &bytes[4..];
        let root = crate::runtime::proto::Digest {
            data: crate::runtime::proto::util::read_bytes_32(bytes)?,
        };
        let sumcheck_proof = SumcheckProof::read(bytes, &geom.sc_geom, f)?;
        let ring_proof = RingSwitch128Proof::read(bytes)?;
        let com_proof = crate::runtime::proto::polygero::read(bytes, &geom.com_geom, f, sf)?;
        Ok(Self {
            sumcheck_proof,
            ring_proof,
            com: PolygeroCommitment { root },
            com_proof,
        })
    }
}
