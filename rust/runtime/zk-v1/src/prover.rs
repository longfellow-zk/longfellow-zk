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

//! Prove a v1 circuit using masked sumcheck followed by Ligero.
//!
//! Commitment fixes the private inputs, each sumcheck message pad, and one pad
//! product per layer. Sumcheck then reduces the circuit to constraints on those
//! committed values. The constraint compiler substitutes public inputs and pad
//! coordinates; Ligero proves the resulting A*w+b=0 and pad-product constraints.
//! The two public phases preserve the legacy transcript and proof layout.

use crate::runtime::{
    algebra::{ElementOf, RangeInterpolatorFactory, SubfieldV1, ZkField},
    ligero::{param::LigeroQuadraticConstraint, LigeroProver},
    random::{RandomEngine, Transcript},
    sumcheck_v1::{prove_core as sumcheck_prove_core, SumcheckProof, TranscriptSumcheck},
    zk_v1::{common::ZkContext, ZkProof},
};

/// A trusted legacy circuit and the configuration for its Ligero commitment.
pub struct ZkProver<const W: usize, F: ZkField<W>> {
    pub circuit: crate::core::proto::circuit::Circuit<F>,
    pub config: crate::runtime::ligero::param::LigeroConfig,
}

/// Private state retained between commitment and proof generation.
/// `com` is the public Merkle commitment; pads and encoded rows stay with the prover.
pub struct ZkCommitResult<const W: usize, F: ZkField<W>> {
    pad: SumcheckProof<W, F>,
    lqc: Vec<LigeroQuadraticConstraint>,
    lp: LigeroProver<W, F>,
    pub com: crate::runtime::proto::ligero::LigeroCommitment,
}

impl<const W: usize, F: ZkField<W>> ZkProver<W, F> {
    pub fn new(
        circuit: crate::core::proto::circuit::Circuit<F>,
        config: crate::runtime::ligero::param::LigeroConfig,
    ) -> Self {
        Self { circuit, config }
    }
    /// Computes ZK commitment of the witness and ZK pads.
    #[allow(clippy::too_many_arguments)]
    pub fn commit<
        IF: RangeInterpolatorFactory<W, F>,
        R: RandomEngine,
        SF: SubfieldV1<E = ElementOf<F>>,
    >(
        &self,
        witness_only: &[ElementOf<F>],
        ctx: &ZkContext<'_, W, F, IF>,
        ts: &mut Transcript,
        rng: &mut R,
        sf: &SF,
    ) -> (
        ZkCommitResult<W, F>,
        crate::runtime::proto::zk_v1::ZkProofGeometry,
    ) {
        assert!(
            self.circuit.raw.ninput >= self.circuit.raw.npublic_input,
            "npublic_input ({}) exceeds ninput ({})",
            self.circuit.raw.npublic_input,
            self.circuit.raw.ninput
        );

        let n_witness = self.circuit.raw.ninput - self.circuit.raw.npublic_input;
        assert_eq!(witness_only.len(), n_witness, "witness length mismatch");

        // The circuit boundary includes public inputs; Ligero commits only private inputs.
        let subfield_boundary = self
            .circuit
            .raw
            .subfield_boundary
            .saturating_sub(self.circuit.raw.npublic_input);

        let sc_geom =
            crate::runtime::proto::sumcheck_v1::SumcheckProofGeometry::from_circuit(&self.circuit);
        let (pad, pad_witness) = crate::runtime::sumcheck_v1::pad::sample(&sc_geom, rng, ctx.f);

        let mut witness = Vec::with_capacity(witness_only.len() + pad_witness.len());
        witness.extend_from_slice(witness_only);
        witness.extend(pad_witness);

        let lqc =
            crate::runtime::zk_v1::constraint_compiler::product_constraints(n_witness, &sc_geom);

        let ligero_param = crate::runtime::ligero::param::LigeroParam::new(
            witness.len(),
            self.circuit.raw.layers.len(),
            self.config,
            ctx.make_interpolator,
        );

        let (lp, com) = crate::runtime::ligero::prover::LigeroProver::commit(
            subfield_boundary,
            &witness,
            ligero_param,
            ts,
            &lqc,
            ctx.make_interpolator,
            rng,
            ctx.f,
            sf,
        );
        let geom = crate::runtime::proto::zk_v1::ZkProofGeometry {
            com_geom: ligero_param.geom,
            sc_geom,
        };
        (ZkCommitResult { pad, lqc, lp, com }, geom)
    }

    /// Generates ZK proof over the committed witness and pads.
    pub fn prove<IF: RangeInterpolatorFactory<W, F>>(
        &self,
        public_inputs: Vec<ElementOf<F>>,
        witness_only: Vec<ElementOf<F>>,
        commit_info: &ZkCommitResult<W, F>,
        tsp: &mut Transcript,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> Result<ZkProof<W, F>, String> {
        assert!(
            self.circuit.raw.ninput >= self.circuit.raw.npublic_input,
            "npublic_input ({}) exceeds ninput ({})",
            self.circuit.raw.npublic_input,
            self.circuit.raw.ninput
        );

        let n_public = self.circuit.raw.npublic_input;
        let n_witness = self.circuit.raw.ninput - self.circuit.raw.npublic_input;
        assert_eq!(
            public_inputs.len(),
            n_public,
            "public inputs length mismatch"
        );
        let mut inputs_and_witnesses = Vec::with_capacity(n_public + n_witness);
        inputs_and_witnesses.extend_from_slice(&public_inputs);
        inputs_and_witnesses.extend(witness_only);

        tsp.write_sumcheck_statement(&self.circuit, &public_inputs, ctx.f);
        let in_layers =
            crate::runtime::sumcheck_v1::eval_circuit(inputs_and_witnesses, &self.circuit, ctx.f)
                .map_err(|e| format!("eval_circuit failed: {e}"))?;

        let (proof, data) =
            sumcheck_prove_core(in_layers, &commit_info.pad, &self.circuit, tsp, ctx.f);

        // Resolve logical pads while the symbolic constraints are live. Only the
        // compiled coefficients and constants are needed during the Ligero proof.
        let (a, b) = {
            let relations = crate::runtime::sumcheck_v1::symbolic::verify(&proof, data, ctx.f)?;
            let geometry = crate::runtime::proto::sumcheck_v1::SumcheckProofGeometry::from_circuit(
                &self.circuit,
            );
            let pads = geometry.pad_layout(n_witness);
            crate::runtime::zk_v1::constraint_compiler::compile(
                &relations,
                &pads,
                &public_inputs,
                ctx.f,
            )?
        };

        let statement_hash = crate::runtime::zk_v1::common::DEFAULT_STATEMENT_HASH;

        let com_proof = commit_info.lp.prove(
            &b,
            tsp,
            &a,
            &statement_hash,
            &commit_info.lqc,
            ctx.make_interpolator,
            ctx.f,
        );

        Ok(ZkProof {
            com: commit_info.com.clone(),
            sumcheck_proof: proof,
            com_proof,
        })
    }
}

#[cfg(test)]
#[path = "../tests/prover.rs"]
mod tests;
