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

use core::fmt;

use runtime_algebra::{ElementOf, InterpolatorFactory, ZkField};
use runtime_ligero::param::{LigeroConfig, LigeroParam};
use runtime_random::Transcript;
use runtime_sumcheck_ng::TranscriptSumcheck;

use crate::{common::ZkContext, ZkProof};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZkVerificationError {
    InvalidSumcheck(String),
    PublicInputLengthMismatch { expected: usize, actual: usize },
    LigeroVerification(String),
}

impl fmt::Display for ZkVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSumcheck(message) => write!(f, "Invalid sumcheck: {message}"),
            Self::PublicInputLengthMismatch { expected, actual } => {
                write!(
                    f,
                    "Public input length mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            Self::LigeroVerification(err) => write!(f, "Ligero commitment proof error: {}", err),
        }
    }
}

impl std::error::Error for ZkVerificationError {}

/// The Zero-Knowledge Verifier.
pub struct ZkVerifier<const W: usize, F: ZkField<W>> {
    pub circuit: core_proto::circuit::Circuit<F>,
    pub config: LigeroConfig,
}

impl<const W: usize, F: ZkField<W>> ZkVerifier<W, F> {
    /// Constructs a new `ZkVerifier` with the given Ligero configuration.
    pub fn new(circuit: core_proto::circuit::Circuit<F>, config: LigeroConfig) -> Self {
        Self { circuit, config }
    }

    fn ligero_param<IF: InterpolatorFactory<W, F>>(
        &self,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> LigeroParam {
        let (nw, nq) = crate::proof::witness_and_constraint_count(&self.circuit);
        LigeroParam::new(nw, nq, self.config, ctx.make_interpolator)
    }

    pub fn geometry<IF: InterpolatorFactory<W, F>>(
        &self,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> crate::proof::ZkProofGeometry {
        crate::proof::ZkProofGeometry {
            sc_geom: runtime_proto::sumcheck_ng::SumcheckProofGeometry::from_circuit(&self.circuit),
            com_geom: self.ligero_param(ctx).geom,
        }
    }

    /// Replays commitment transmission from P to V.
    pub fn recv_commitment<IF: InterpolatorFactory<W, F>>(
        &self,
        zkp: &ZkProof<W, F>,
        tv: &mut Transcript,
        ctx: &ZkContext<'_, W, F, IF>,
    ) {
        let ligero_param = self.ligero_param(ctx);
        let mut lv = runtime_ligero::LigeroVerifier::new(tv, &ligero_param);
        lv.receive_commitment(&zkp.com);
    }

    /// Verifies ZK proof against public inputs and circuit.
    pub fn verify<IF: InterpolatorFactory<W, F>>(
        &self,
        pub_inputs: Vec<ElementOf<F>>,
        zkp: &ZkProof<W, F>,
        tv: &mut Transcript,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> Result<(), ZkVerificationError> {
        assert!(
            self.circuit.raw.ninput >= self.circuit.raw.npublic_input,
            "npublic_input ({}) exceeds ninput ({})",
            self.circuit.raw.npublic_input,
            self.circuit.raw.ninput
        );

        if pub_inputs.len() != self.circuit.raw.npublic_input {
            return Err(ZkVerificationError::PublicInputLengthMismatch {
                expected: self.circuit.raw.npublic_input,
                actual: pub_inputs.len(),
            });
        }
        tv.write_sumcheck_statement(&self.circuit, &pub_inputs, ctx.f);
        let data = runtime_sumcheck_ng::derive_verifier_data(
            &self.circuit,
            &zkp.sumcheck_proof,
            tv,
            ctx.f,
        )
        .map_err(ZkVerificationError::InvalidSumcheck)?;
        let n_witness = self.circuit.raw.ninput - self.circuit.raw.npublic_input;
        let geometry =
            runtime_proto::sumcheck_ng::SumcheckProofGeometry::from_circuit(&self.circuit);
        let relations = runtime_sumcheck_ng::symbolic::verify(&zkp.sumcheck_proof, data, ctx.f)
            .map_err(ZkVerificationError::InvalidSumcheck)?;
        let pads = geometry.pad_layout(n_witness);
        let (a, b) = crate::constraint_compiler::compile(&relations, &pads, &pub_inputs, ctx.f)
            .map_err(ZkVerificationError::InvalidSumcheck)?;

        let statement_hash = crate::common::DEFAULT_STATEMENT_HASH;

        let ligero_param = self.ligero_param(ctx);
        let lqc = crate::constraint_compiler::product_constraints(n_witness, &geometry);

        let mut lv = runtime_ligero::LigeroVerifier::new(tv, &ligero_param);
        lv.verify(
            &b,
            &zkp.com,
            &zkp.com_proof,
            &a,
            &statement_hash,
            &lqc,
            ctx.make_interpolator,
            ctx.f,
        )
        .map_err(|e| ZkVerificationError::LigeroVerification(format!("{e:?}")))
    }
}
