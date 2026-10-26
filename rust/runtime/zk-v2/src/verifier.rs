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

//! Verify sumcheck constraints against the witness committed by Polygero.
//!
//! Construction validates the commitment dimensions and prepares the proof
//! geometry from a trusted circuit. Receive the proof's root before continuing
//! the shared transcript. Verification then binds public inputs, reconstructs
//! sumcheck's symbolic constraints, samples their source-statement identifier,
//! and compiles them into sparse A and b.
//!
//! Polygero checks A*w+b=0 and the pad-product constraints fixed at construction.
//! Reconstructing sumcheck constraints is not itself an acceptance test; the
//! complete proof is accepted only after Polygero verifies. Symbolic expressions
//! and pad coordinates are local to compilation and end before that final check.
use core::fmt;

use crate::{
    core::proto::circuit::Circuit,
    runtime::{
        algebra::{ElementOf, EvaluationDomain, ZkField},
        polygero::{PolygeroConfig, PolygeroLinearTerm, PolygeroVerifier},
        proto::Digest,
        random::Transcript,
        sumcheck_v2::{self, TranscriptSumcheck},
        zk_v2::{
            constraint_compiler,
            context::{prepare_layout, private_input_count},
            ZkContext, ZkProof, ZkProofGeometry,
        },
    },
};

/// Immutable circuit, proof geometry and prepared Polygero verifier.
/// Public parameters are validated once, before decoding or receiving a proof.
pub struct ZkVerifier<const W: usize, F: ZkField<W>> {
    circuit: Circuit<F>,
    geometry: ZkProofGeometry,
    polygero: PolygeroVerifier,
}

impl<const W: usize, F: ZkField<W>> ZkVerifier<W, F> {
    /// Prepare the public layout once, before decoding or receiving a proof.
    pub fn new<D: EvaluationDomain<W, F>>(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<Self, ZkVerificationError> {
        let (geometry, param) = prepare_layout(&circuit, config, ctx)
            .map_err(ZkVerificationError::PolygeroVerification)?;
        Ok(Self {
            circuit,
            geometry,
            polygero: PolygeroVerifier::new(param),
        })
    }

    /// Return the validated sizes used by the proof codec.
    pub fn geometry(&self) -> ZkProofGeometry {
        self.geometry.clone()
    }

    /// Public prefix length used by application input validation.
    pub(crate) fn public_input_count(&self) -> usize {
        self.circuit.raw.npublic_input
    }

    /// Receive this proof's root before sumcheck and remember it for verification.
    pub fn receive_commitment(&mut self, proof: &ZkProof<W, F>, transcript: &mut Transcript) {
        self.polygero.receive_commitment(&proof.com, transcript);
    }

    /// Verify against public inputs using the circuit and parameters prepared at construction.
    pub fn verify<D: EvaluationDomain<W, F>>(
        &self,
        public_inputs: &[ElementOf<F>],
        proof: &ZkProof<W, F>,
        transcript: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<(), ZkVerificationError> {
        self.validate(public_inputs, proof)?;
        #[cfg(feature = "bench-profile")]
        let mut profile =
            crate::util::profile::Timer::new(format!("zk{W}.verifier.gkr_and_constraints"));
        let (a, b, statement) =
            self.compile_constraints(public_inputs, proof, transcript, ctx.f)?;
        #[cfg(feature = "bench-profile")]
        profile.next(format!("zk{W}.verifier.backend_and_cleanup"));
        self.polygero
            .verify(
                &b,
                &proof.com,
                &proof.com_proof,
                &a,
                &statement,
                transcript,
                ctx.domain,
                ctx.f,
            )
            .map_err(|e| ZkVerificationError::PolygeroVerification(e.to_string()))
    }

    /// Check input and message lengths before advancing the transcript.
    /// The two protocols still validate their inputs when used independently.
    fn validate(
        &self,
        public_inputs: &[F::E],
        proof: &ZkProof<W, F>,
    ) -> Result<(), ZkVerificationError> {
        if public_inputs.len() != self.public_input_count() {
            return Err(ZkVerificationError::PublicInputLengthMismatch {
                expected: self.public_input_count(),
                actual: public_inputs.len(),
            });
        }
        proof
            .sumcheck_proof
            .validate(&self.geometry.sc_geom)
            .map_err(|error| ZkVerificationError::InvalidSumcheck(error.to_string()))?;
        proof
            .com_proof
            .validate(&self.geometry.com_geom)
            .map_err(|e| ZkVerificationError::PolygeroVerification(e.to_string()))
    }

    /// Reconstruct sumcheck, sample its statement identifier, then compile A*w+b=0.
    /// Symbolic expressions and pad coordinates stay in this phase.
    fn compile_constraints(
        &self,
        public_inputs: &[F::E],
        proof: &ZkProof<W, F>,
        transcript: &mut Transcript,
        f: &F,
    ) -> Result<(Vec<PolygeroLinearTerm<F::E>>, Vec<F::E>, Digest), ZkVerificationError> {
        transcript.write_sumcheck_statement(&self.circuit, public_inputs, f);
        let constraints =
            sumcheck_v2::derive_constraints(&self.circuit, &proof.sumcheck_proof, transcript, f)
                .map_err(ZkVerificationError::InvalidSumcheck)?;
        let statement = super::transcript::statement_digest(transcript);
        let pads = self
            .geometry
            .sc_geom
            .pad_layout(private_input_count(&self.circuit));
        let (a, b) = constraint_compiler::compile(&constraints, &pads, public_inputs, f)
            .map_err(ZkVerificationError::InvalidSumcheck)?;
        Ok((a, b, statement))
    }
}

/// Failures in public input shape, sumcheck reconstruction, or commitment verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZkVerificationError {
    InvalidSumcheck(String),
    PublicInputLengthMismatch { expected: usize, actual: usize },
    PolygeroVerification(String),
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
            Self::PolygeroVerification(err) => {
                write!(f, "Polygero commitment proof error: {}", err)
            }
        }
    }
}

impl std::error::Error for ZkVerificationError {}
