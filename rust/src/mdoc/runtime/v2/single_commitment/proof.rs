// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Complete codec for one binary commitment and two arithmetic frontends.
use super::constants::QUOTIENT_BITS;
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128, Gf2_128Field},
            p256::P256Field,
        },
        v2::{
            foreign::word::MaskedWord,
            proto::{
                polygero::{
                    FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig,
                    PolygeroGeometry,
                },
                sumcheck::{SumcheckProof, SumcheckProofGeometry},
                witness_selection::{FingerprintResponse, FINGERPRINTS},
                zk::{CircuitProof, CircuitProofGeometry},
            },
        },
    },
};
/// Trusted dimensions, checked before a single-commitment proof is read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofGeometry {
    binary: CircuitProofGeometry,
    signature: SumcheckProofGeometry,
    config: PolygeroConfig,
    polygero: PolygeroGeometry,
}
impl ProofGeometry {
    pub(super) fn new(
        binary: CircuitProofGeometry,
        signature: SumcheckProofGeometry,
        config: PolygeroConfig,
    ) -> Result<Self, String> {
        let polygero = PolygeroGeometry::new(binary.nw(), config).map_err(|e| e.to_string())?;
        Ok(Self {
            binary,
            signature,
            config,
            polygero,
        })
    }
    pub fn binary(&self) -> &CircuitProofGeometry {
        &self.binary
    }
    pub fn signature(&self) -> &SumcheckProofGeometry {
        &self.signature
    }
    pub fn config(&self) -> PolygeroConfig {
        self.config
    }
    pub fn polygero(&self) -> PolygeroGeometry {
        self.polygero
    }
    fn fixed_len(&self, f: &Gf2_128Field, p: &P256Field) -> Option<usize> {
        let width = f.serialized_size_bytes();
        let [response, rows] = FieldProof::<()>::wire_lengths(&self.polygero, width)?;
        [
            Some(32),
            FINGERPRINTS.checked_mul(width),
            self.signature
                .serialized_elements()
                .checked_mul(p.serialized_size_bytes()),
            Some(2 * QUOTIENT_BITS.div_ceil(8)),
            self.binary.proof_len(width),
            Some(response),
            Some(rows),
            JointPolygeroProof::<()>::fixed_opening_len(self.config.t),
        ]
        .into_iter()
        .try_fold(0usize, |total, x| total.checked_add(x?))
    }
}
pub(super) struct Proof {
    pub commitment: PolygeroCommitment,
    pub fingerprints: FingerprintResponse<Gf2_128>,
    pub signature: SumcheckProof<P256Field>,
    pub masked: [MaskedWord<QUOTIENT_BITS>; 2],
    pub binary: CircuitProof<Gf2_128Field>,
    pub polygero: JointPolygeroProof<(FieldProof<Gf2_128>, ())>,
}

impl Proof {
    const MAGIC: &'static [u8; 7] = b"MDSC003";
}
cfg_prover! {mod prover;}
cfg_verifier! {mod verifier;}
