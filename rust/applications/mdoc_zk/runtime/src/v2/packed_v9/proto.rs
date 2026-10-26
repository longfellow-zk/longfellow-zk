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

//! v9 application encoding: six MAC tags, LFB2 flat-trace hash proof, LFV2 signature proof.
pub use crate::mdoc::runtime::v2::proto::MdocProofGeometry;
use crate::runtime::{
    algebra::{
        gf2_128::{Gf2_128, Gf2_128Field},
        p256::P256Field,
        Subfield,
    },
    proto::{packed_zk::PackedZkProof, zk_v2::ZkProof},
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocProof {
    pub macs: [u128; 6],
    pub proof_hash: PackedZkProof,
    pub proof_sig: ZkProof<4, P256Field>,
}
impl MdocProof {
    pub fn write<
        SF1: Subfield<E = Gf2_128>,
        SF2: Subfield<E = crate::runtime::algebra::p256::P256Element>,
    >(
        &self,
        g: &MdocProofGeometry,
        f: &Gf2_128Field,
        sf: &SF1,
        p: &P256Field,
        psf: &SF2,
    ) -> Result<Vec<u8>, String> {
        let mut b = Vec::new();
        for m in self.macs {
            b.extend_from_slice(&m.to_le_bytes())
        }
        self.proof_hash
            .write_to_buf(&mut b, &g.geom_hash, f, sf)
            .map_err(|e| e.to_string())?;
        self.proof_sig
            .write_to_buf(&mut b, &g.geom_sig, p, psf)
            .map_err(|e| e.to_string())?;
        Ok(b)
    }
    pub fn read<
        'a,
        SF1: Subfield<E = Gf2_128>,
        SF2: Subfield<E = crate::runtime::algebra::p256::P256Element>,
    >(
        bytes: &'a [u8],
        g: &MdocProofGeometry,
        f: &Gf2_128Field,
        sf: &SF1,
        p: &P256Field,
        psf: &SF2,
    ) -> Result<(&'a [u8], Self), String> {
        if bytes.len() < 96 {
            return Err("truncated v9 MAC tags".into());
        }
        let macs = std::array::from_fn(|i| {
            u128::from_le_bytes(bytes[i * 16..i * 16 + 16].try_into().unwrap())
        });
        let mut rest = &bytes[96..];
        let proof_hash =
            PackedZkProof::read(&mut rest, &g.geom_hash, f, sf).map_err(|e| e.to_string())?;
        let proof_sig = ZkProof::read(&mut rest, &g.geom_sig, p, psf).map_err(|e| e.to_string())?;
        Ok((
            rest,
            Self {
                macs,
                proof_hash,
                proof_sig,
            },
        ))
    }
}
