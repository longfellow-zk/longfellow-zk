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

//! Verify a v1 proof by translating masked sumcheck into Ligero constraints.
//!
//! After the commitment is absorbed, replay sumcheck using the circuit and public
//! inputs. Its masked messages determine symbolic equations in the hidden pads;
//! compiling these equations yields A*w+b=0 over the committed witness. Ligero
//! checks these equations together with each layer's pad-product constraint.
//! Proof dimensions are checked before any transcript replay or message indexing.

use core::fmt;

use crate::runtime::{
    algebra::{ElementOf, RangeInterpolatorFactory, ZkField},
    v1::{
        ligero::param::{LigeroConfig, LigeroParam},
        sumcheck::TranscriptSumcheck,
        transcript::Transcript,
        zk::{common::ZkContext, ZkProof},
    },
};

/// A trusted legacy circuit and the configuration used to decode its commitment.
pub struct ZkVerifier<const W: usize, F: ZkField<W>> {
    pub circuit: crate::core::proto::v1::Circuit<F>,
    pub config: LigeroConfig,
}

impl<const W: usize, F: ZkField<W>> ZkVerifier<W, F> {
    /// Constructs a new `ZkVerifier` with the given Ligero configuration.
    pub fn new(circuit: crate::core::proto::v1::Circuit<F>, config: LigeroConfig) -> Self {
        Self { circuit, config }
    }

    /// Derive the legacy proof dimensions from the trusted circuit and configuration.
    pub fn geometry<IF: RangeInterpolatorFactory<W, F>>(
        &self,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> crate::runtime::v1::proto::zk::ZkProofGeometry {
        crate::runtime::v1::proto::zk::ZkProofGeometry {
            sc_geom: crate::runtime::v1::proto::sumcheck::SumcheckProofGeometry::from_circuit(
                &self.circuit,
            ),
            com_geom: self.ligero_param(ctx).geom,
        }
    }

    /// Replays commitment transmission from P to V.
    pub fn recv_commitment<IF: RangeInterpolatorFactory<W, F>>(
        &self,
        zkp: &ZkProof<W, F>,
        tv: &mut Transcript,
        ctx: &ZkContext<'_, W, F, IF>,
    ) {
        let ligero_param = self.ligero_param(ctx);
        let mut lv = crate::runtime::v1::ligero::LigeroVerifier::new(tv, &ligero_param);
        lv.receive_commitment(&zkp.com);
    }

    /// Verifies ZK proof against public inputs and circuit.
    pub fn verify<IF: RangeInterpolatorFactory<W, F>>(
        &self,
        pub_inputs: Vec<ElementOf<F>>,
        zkp: &ZkProof<W, F>,
        tv: &mut Transcript,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> Result<(), ZkVerificationError> {
        self.validate(pub_inputs.len(), zkp)?;

        tv.write_sumcheck_statement(&self.circuit, &pub_inputs, ctx.f);
        let n_witness = self.circuit.raw.ninput - self.circuit.raw.npublic_input;
        // Only compiled coefficients and the pad geometry survive this phase.
        // The transcript data and symbolic terms can be released before Ligero.
        let (geometry, a, b) = {
            let data = crate::runtime::v1::sumcheck::derive_verifier_data(
                &self.circuit,
                &zkp.sumcheck_proof,
                tv,
                ctx.f,
            )
            .map_err(ZkVerificationError::InvalidSumcheck)?;
            let relations =
                crate::runtime::v1::sumcheck::symbolic::verify(&zkp.sumcheck_proof, data, ctx.f)
                    .map_err(ZkVerificationError::InvalidSumcheck)?;
            let geometry = crate::runtime::v1::proto::sumcheck::SumcheckProofGeometry::from_circuit(
                &self.circuit,
            );
            let pads = geometry.pad_layout(n_witness);
            let (a, b) = crate::runtime::v1::zk::constraint_compiler::compile(
                &relations,
                &pads,
                &pub_inputs,
                ctx.f,
            )
            .map_err(ZkVerificationError::InvalidSumcheck)?;
            (geometry, a, b)
        };

        let statement_hash = crate::runtime::v1::zk::common::DEFAULT_STATEMENT_HASH;

        let ligero_param = self.ligero_param(ctx);
        let lqc =
            crate::runtime::v1::zk::constraint_compiler::product_constraints(n_witness, &geometry);

        let mut lv = crate::runtime::v1::ligero::LigeroVerifier::new(tv, &ligero_param);
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

    /// Check public-input and sumcheck message dimensions in legacy error order.
    fn validate(&self, npublic: usize, zkp: &ZkProof<W, F>) -> Result<(), ZkVerificationError> {
        assert!(
            self.circuit.raw.ninput >= self.circuit.raw.npublic_input,
            "npublic_input ({}) exceeds ninput ({})",
            self.circuit.raw.npublic_input,
            self.circuit.raw.ninput
        );
        if npublic != self.circuit.raw.npublic_input {
            return Err(ZkVerificationError::PublicInputLengthMismatch {
                expected: self.circuit.raw.npublic_input,
                actual: npublic,
            });
        }
        if zkp.sumcheck_proof.layers.len() != self.circuit.raw.layers.len() {
            return Err(ZkVerificationError::SumcheckProofLayerMismatch {
                expected: self.circuit.raw.layers.len(),
                actual: zkp.sumcheck_proof.layers.len(),
            });
        }
        for layer in 0..self.circuit.raw.layers.len() {
            let message = &zkp.sumcheck_proof.layers[layer];
            let logw = self.circuit.raw.layers[layer].logw();
            if message.hp[0].len() != logw || message.hp[1].len() != logw {
                return Err(ZkVerificationError::SumcheckProofRoundMismatch {
                    layer,
                    expected: logw,
                    actual: message.hp[0].len(),
                });
            }
        }
        Ok(())
    }

    /// Count committed private inputs, pads, and pad products using the v1 layout.
    fn ligero_param<IF: RangeInterpolatorFactory<W, F>>(
        &self,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> LigeroParam {
        let (nw, nq) = crate::runtime::v1::proto::zk::witness_and_constraint_count(&self.circuit);
        LigeroParam::new(nw, nq, self.config, ctx.make_interpolator)
    }
}

/// A malformed sumcheck message or a failed Ligero check in the v1 verifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZkVerificationError {
    SumcheckProofLayerMismatch {
        expected: usize,
        actual: usize,
    },
    SumcheckProofRoundMismatch {
        layer: usize,
        expected: usize,
        actual: usize,
    },
    PublicInputLengthMismatch {
        expected: usize,
        actual: usize,
    },
    InvalidSumcheck(String),
    LigeroVerification(String),
}

impl fmt::Display for ZkVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SumcheckProofLayerMismatch { expected, actual } => {
                write!(
                    f,
                    "Sumcheck proof layer count mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            Self::SumcheckProofRoundMismatch {
                layer,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "Sumcheck proof round count mismatch in layer {}: expected {}, got {}",
                    layer, expected, actual
                )
            }
            Self::PublicInputLengthMismatch { expected, actual } => {
                write!(
                    f,
                    "Public input length mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            Self::InvalidSumcheck(err) => write!(f, "Invalid sumcheck: {err}"),
            Self::LigeroVerification(err) => write!(f, "Ligero commitment proof error: {}", err),
        }
    }
}

impl std::error::Error for ZkVerificationError {}
