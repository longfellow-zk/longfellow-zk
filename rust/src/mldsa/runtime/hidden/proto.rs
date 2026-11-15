// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One binary commitment, the native and SIMD reductions, masked adapter
//! quotients, and the complete proof seal.
use super::Circuits;
use crate::{
    core::algebra::SerializableField,
    mldsa::proto::CLAIMS,
    runtime::{
        algebra::{
            fp24_ext6::{RuntimeFp24Ext6, RuntimeFp24Ext6 as AF},
            RuntimeField,
        },
        v2::{
            foreign::word::MaskedWord,
            proto as v2_proto,
            proto::{
                polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig},
                sumcheck::{SumcheckProof, SumcheckProofGeometry},
                zk::{CircuitProof, CircuitProofGeometry},
            },
            transcript as proof_transcript,
            zk::split::pure::PureSplit,
        },
    },
};

pub(super) struct Geometry {
    pub simd_rounds: Option<usize>,
    pub binary: CircuitProofGeometry,
    pub native: SumcheckProofGeometry,
    pub config: PolygeroConfig,
}

pub(super) struct Proof<F1: SerializableField> {
    pub simd: Option<v2_proto::sumcheck::PackedReduction<F1>>,
    pub native: SumcheckProof<AF>,
    pub masked: [MaskedWord<{ super::HQ }>; CLAIMS],
    pub commitment: PolygeroCommitment,
    pub fingerprints: v2_proto::witness_selection::FingerprintResponse<F1::E>,
    pub binary: CircuitProof<F1>,
    pub polygero: JointPolygeroProof<(FieldProof<F1::E>, ())>,
}

pub(super) fn geometry(
    c: &Circuits,
    binary: CircuitProofGeometry,
    native: &PureSplit<RuntimeFp24Ext6>,
) -> Geometry {
    Geometry {
        simd_rounds: c.simd.as_ref().map(|s| s.program().rounds()),
        binary,
        native: native.geometry().sumcheck().clone(),
        config: c.config,
    }
}

cfg_prover! { mod prover; }
cfg_verifier! { mod verifier; }
