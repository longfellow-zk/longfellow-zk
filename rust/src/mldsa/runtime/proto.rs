// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One binary commitment, masked adapter quotients, and the complete proof seal.
use super::Circuits;
use crate::{
    core::algebra::SerializableField,
    mldsa::proto::CLAIMS,
    runtime::{
        algebra::RuntimeField,
        v2::{
            foreign::word::MaskedWord,
            proto as v2_proto,
            proto::{
                polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig},
                sumcheck::{PackedReduction, SumcheckProof, SumcheckProofGeometry},
                zk::{CircuitProof, CircuitProofGeometry},
            },
            transcript as proof_transcript,
        },
    },
};
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Geometry {
    pub simd_rounds: Option<usize>,
    pub binary: CircuitProofGeometry,
    pub config: PolygeroConfig,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Proof<F1: SerializableField> {
    pub simd: Option<PackedReduction<F1>>,
    pub masked: [MaskedWord<{ super::QB }>; CLAIMS],
    pub commitment: PolygeroCommitment,
    pub fingerprints: v2_proto::witness_selection::FingerprintResponse<F1::E>,
    pub binary: CircuitProof<F1>,
    pub polygero: JointPolygeroProof<(FieldProof<F1::E>, ())>,
}

pub(super) fn geometry(c: &Circuits, binary: CircuitProofGeometry) -> Geometry {
    Geometry {
        simd_rounds: c.source.as_ref().map(|s| s.program().rounds()),
        binary,
        config: c.config,
    }
}

cfg_prover! { mod prover; }
cfg_verifier! { mod verifier; }
