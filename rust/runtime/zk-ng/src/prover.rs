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

use runtime_algebra::{ElementOf, InterpolatorFactory, Subfield, ZkField};
use runtime_ligero::{param::LigeroQuadraticConstraint, LigeroProver};
use runtime_random::{RandomEngine, Transcript};
use runtime_sumcheck_ng::{SumcheckProof, TranscriptSumcheck};

use crate::{common::ZkContext, ZkProof};

/// The Zero-Knowledge Prover.
pub struct ZkProver<const W: usize, F: ZkField<W>> {
    pub circuit: core_proto::circuit::Circuit<F>,
    pub config: runtime_ligero::param::LigeroConfig,
}

pub struct ZkCommitResult<const W: usize, F: ZkField<W>> {
    pad: SumcheckProof<W, F>,
    lqc: Vec<LigeroQuadraticConstraint>,
    lp: LigeroProver<W, F>,
    pub com: runtime_proto::ligero::LigeroCommitment,
}

impl<const W: usize, F: ZkField<W>> ZkProver<W, F> {
    pub fn new(
        circuit: core_proto::circuit::Circuit<F>,
        config: runtime_ligero::param::LigeroConfig,
    ) -> Self {
        Self { circuit, config }
    }

    /// Computes ZK commitment of the witness and ZK pads.
    #[allow(clippy::too_many_arguments)]
    pub fn commit<
        IF: InterpolatorFactory<W, F>,
        R: RandomEngine,
        SF: Subfield<E = ElementOf<F>>,
    >(
        &self,
        witness_only: &[ElementOf<F>],
        ctx: &ZkContext<'_, W, F, IF>,
        ts: &mut Transcript,
        rng: &mut R,
        sf: &SF,
    ) -> (ZkCommitResult<W, F>, crate::proof::ZkProofGeometry) {
        assert!(
            self.circuit.raw.ninput >= self.circuit.raw.npublic_input,
            "npublic_input ({}) exceeds ninput ({})",
            self.circuit.raw.npublic_input,
            self.circuit.raw.ninput
        );

        let n_witness = self.circuit.raw.ninput - self.circuit.raw.npublic_input;
        assert_eq!(witness_only.len(), n_witness, "witness length mismatch");

        // Rebase the subfield boundary to private witnesses
        let subfield_boundary = self
            .circuit
            .raw
            .subfield_boundary
            .saturating_sub(self.circuit.raw.npublic_input);

        let sc_geom =
            runtime_proto::sumcheck_ng::SumcheckProofGeometry::from_circuit(&self.circuit);
        let (pad, pad_witness) = runtime_sumcheck_ng::pad::sample(&sc_geom, rng, ctx.f);

        let mut witness = witness_only.to_vec();
        witness.extend(pad_witness);

        let lqc = crate::constraint_compiler::product_constraints(n_witness, &sc_geom);

        let ligero_param = runtime_ligero::param::LigeroParam::new(
            witness.len(),
            self.circuit.raw.layers.len(),
            self.config,
            ctx.make_interpolator,
        );

        let (lp, com) = runtime_ligero::prover::LigeroProver::commit(
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
        let geom = crate::proof::ZkProofGeometry {
            com_geom: ligero_param.geom,
            sc_geom,
        };
        (ZkCommitResult { pad, lqc, lp, com }, geom)
    }

    /// Generates ZK proof over the committed witness and pads.
    pub fn prove<IF: InterpolatorFactory<W, F>>(
        &self,
        public_inputs: Vec<ElementOf<F>>,
        witness_only: Vec<ElementOf<F>>,
        commit_info: &ZkCommitResult<W, F>,
        tsp: &mut Transcript,
        ctx: &ZkContext<'_, W, F, IF>,
    ) -> Result<ZkProof<W, F>, String> {
        let geometry =
            runtime_proto::sumcheck_ng::SumcheckProofGeometry::from_circuit(&self.circuit);
        commit_info
            .pad
            .validate(&geometry)
            .map_err(|error| error.to_string())?;
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
        assert_eq!(witness_only.len(), n_witness, "witness length mismatch");
        let mut inputs_and_witnesses = Vec::with_capacity(n_public + n_witness);
        inputs_and_witnesses.extend_from_slice(&public_inputs);
        inputs_and_witnesses.extend(witness_only);

        tsp.write_sumcheck_statement(&self.circuit, &public_inputs, ctx.f);
        let evaluated =
            runtime_sumcheck_ng::eval_circuit(inputs_and_witnesses, &self.circuit, ctx.f)
                .map_err(|e| format!("eval_circuit failed: {e}"))?;
        let (proof, data) =
            runtime_sumcheck_ng::prove_core(evaluated, &commit_info.pad, &self.circuit, tsp, ctx.f);
        let relations = runtime_sumcheck_ng::symbolic::verify(&proof, data, ctx.f)?;
        let pads = geometry.pad_layout(n_witness);
        let (a, b) = crate::constraint_compiler::compile(&relations, &pads, &public_inputs, ctx.f)?;

        let statement_hash = crate::common::DEFAULT_STATEMENT_HASH;

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
mod tests {
    use super::*;
    use core_algebra::AlgebraicField;
    use core_proto::{
        circuit::{Circuit, RawCircuit},
        Layer, TermDelta,
    };
    use runtime_algebra::{
        gf2_128::Gf2_128Field, lch14_reed_solomon::Lch14InterpolatorFactory,
        subfield::BinarySubfield,
    };

    #[test]
    fn zk_prover_matches_numerical_prover_and_symbolic_verifier() {
        let f = Gf2_128Field::new();
        let sf = BinarySubfield::new(&core_algebra::proto::GF2_16_BASIS_V1);
        let interpolation = Lch14InterpolatorFactory::new(&f, &sf);
        let context = ZkContext {
            f: &f,
            make_interpolator: &interpolation,
        };
        let circuit = Circuit {
            id: [0; 32],
            raw: RawCircuit {
                ninput: 4,
                npublic_input: 1,
                noutput: 2,
                logv: 1,
                subfield_boundary: 0,
                constants: vec![f.zero(), f.one()],
                layers: vec![Layer::new_compressed(
                    4,
                    2,
                    vec![vec![
                        TermDelta {
                            g: 0,
                            h: [0, 1],
                            k_index: 1,
                        },
                        TermDelta {
                            g: 1,
                            h: [2, 1],
                            k_index: 0,
                        },
                    ]],
                    vec![0],
                )],
            },
        };
        let prover = ZkProver::new(
            circuit,
            runtime_ligero::LigeroConfig {
                rateinv: 4,
                nreq: 16,
                block_enc: 256,
            },
        );
        let public = vec![f.one()];
        let witness = vec![f.zero(), f.zero(), f.one()];
        let mut transcript = Transcript::new(b"numerical-symbolic-equivalence");
        let (committed, geometry) = prover.commit(
            &witness,
            &context,
            &mut transcript,
            &mut runtime_random::DeterministicRng::new(42),
            &sf,
        );
        let (nw, nq) = crate::proof::witness_and_constraint_count(&prover.circuit);
        let param = runtime_ligero::param::LigeroParam::new(nw, nq, prover.config, &interpolation);
        let mut numerical = Transcript::new(b"numerical-symbolic-equivalence");
        let mut independent = Transcript::new(b"numerical-symbolic-equivalence");
        for stream in [&mut numerical, &mut independent] {
            {
                let mut receiver = runtime_ligero::LigeroVerifier::new(stream, &param);
                receiver.receive_commitment(&committed.com);
            }
            stream.write_sumcheck_statement(&prover.circuit, &public, &f);
        }
        let actual = prover
            .prove(
                public.clone(),
                witness.clone(),
                &committed,
                &mut transcript,
                &context,
            )
            .unwrap();

        let mut fingerprint = Transcript::new(b"ng-proof-compatibility");
        fingerprint.write_bytes(&actual.write(&geometry, &f, &sf).unwrap());
        assert_eq!(
            fingerprint.bytes(32),
            [
                170, 166, 117, 54, 34, 59, 194, 90, 147, 249, 12, 250, 209, 87, 42, 218, 53, 117,
                147, 197, 154, 76, 215, 68, 66, 129, 193, 202, 99, 39, 242, 84
            ]
        );
        let actual_state = transcript.bytes(32);
        assert_eq!(
            actual_state,
            [
                106, 65, 245, 166, 240, 125, 176, 0, 67, 125, 208, 67, 24, 51, 242, 7, 169, 205,
                254, 33, 88, 12, 246, 99, 237, 82, 250, 170, 92, 140, 127, 189
            ]
        );

        let mut inputs = public.clone();
        inputs.extend(witness);
        let layers = runtime_sumcheck_ng::eval_circuit(inputs, &prover.circuit, &f).unwrap();
        let (proof, data) = runtime_sumcheck_ng::prove_core(
            layers,
            &committed.pad,
            &prover.circuit,
            &mut numerical,
            &f,
        );
        let derived = runtime_sumcheck_ng::derive_verifier_data(
            &prover.circuit,
            &proof,
            &mut independent,
            &f,
        )
        .unwrap();
        assert_eq!(data, derived);
        let pads = geometry.sc_geom.pad_layout(3);
        let relations = runtime_sumcheck_ng::symbolic::verify(&proof, data, &f).unwrap();
        let independent_relations =
            runtime_sumcheck_ng::symbolic::verify(&proof, derived, &f).unwrap();
        let (prover_a, prover_b) =
            crate::constraint_compiler::compile(&relations, &pads, &public, &f).unwrap();
        let (a, b) =
            crate::constraint_compiler::compile(&independent_relations, &pads, &public, &f)
                .unwrap();
        assert_eq!(prover_b, b);
        assert_eq!(prover_a.len(), a.len());
        for (left, right) in prover_a.iter().zip(&a) {
            assert_eq!((left.c, left.w, left.k), (right.c, right.w, right.k));
        }
        let com_proof = committed.lp.prove(
            &b,
            &mut numerical,
            &a,
            &crate::common::DEFAULT_STATEMENT_HASH,
            &committed.lqc,
            &interpolation,
            &f,
        );
        let expected = ZkProof {
            com: committed.com.clone(),
            sumcheck_proof: proof,
            com_proof,
        };
        assert_eq!(
            actual.write(&geometry, &f, &sf).unwrap(),
            expected.write(&geometry, &f, &sf).unwrap()
        );
        {
            let mut verifier = runtime_ligero::LigeroVerifier::new(&mut independent, &param);
            verifier
                .verify(
                    &b,
                    &actual.com,
                    &actual.com_proof,
                    &a,
                    &crate::common::DEFAULT_STATEMENT_HASH,
                    &committed.lqc,
                    &interpolation,
                    &f,
                )
                .unwrap();
        }
        assert_eq!(actual_state, numerical.bytes(32));
        assert_eq!(actual_state, independent.bytes(32));
    }
}
