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

use super::*;
use crate::{
    core::{
        algebra::AlgebraicField,
        proto::{
            circuit::{Circuit, RawCircuit},
            Layer, TermDelta,
        },
    },
    runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield_v1::BinarySubfield,
    },
};

#[test]
fn zk_prover_matches_numerical_prover_and_symbolic_verifier() {
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let interpolation = BinaryInterpolatorFactory::new(&f, &sf);
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
        crate::runtime::ligero::LigeroConfig {
            rateinv: 4,
            nreq: 16,
            block_enc: 256,
        },
    );
    let public = vec![f.one()];
    let witness = vec![f.zero(), f.zero(), f.one()];
    let mut transcript = Transcript::new(b"legacy-symbolic-equivalence");
    let (committed, geometry) = prover.commit(
        &witness,
        &context,
        &mut transcript,
        &mut crate::runtime::random::DeterministicRng::new(42),
        &sf,
    );
    let (nw, nq) = crate::runtime::proto::zk_v1::witness_and_constraint_count(&prover.circuit);
    let param =
        crate::runtime::ligero::param::LigeroParam::new(nw, nq, prover.config, &interpolation);
    let mut numerical = Transcript::new(b"legacy-symbolic-equivalence");
    let mut independent = Transcript::new(b"legacy-symbolic-equivalence");
    for stream in [&mut numerical, &mut independent] {
        {
            let mut receiver = crate::runtime::ligero::LigeroVerifier::new(stream, &param);
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

    let mut fingerprint = Transcript::new(b"legacy-proof-compatibility");
    fingerprint.write_bytes(&actual.write(&geometry, &f, &sf).unwrap());
    assert_eq!(
        fingerprint.bytes(32),
        [
            167, 99, 13, 239, 36, 202, 246, 131, 253, 106, 239, 6, 167, 44, 133, 150, 175, 141,
            233, 129, 251, 131, 231, 184, 11, 25, 208, 59, 90, 168, 150, 230
        ]
    );
    let actual_state = transcript.bytes(32);
    assert_eq!(
        actual_state,
        [
            121, 112, 111, 213, 229, 49, 69, 145, 152, 194, 223, 3, 16, 119, 139, 93, 211, 47, 200,
            13, 13, 122, 190, 117, 112, 186, 129, 247, 209, 26, 111, 114
        ]
    );

    let mut inputs = public.clone();
    inputs.extend(witness);
    let layers = crate::runtime::sumcheck_v1::eval_circuit(inputs, &prover.circuit, &f).unwrap();
    let (proof, data) = crate::runtime::sumcheck_v1::prove_core(
        layers,
        &committed.pad,
        &prover.circuit,
        &mut numerical,
        &f,
    );
    let derived = crate::runtime::sumcheck_v1::derive_verifier_data(
        &prover.circuit,
        &proof,
        &mut independent,
        &f,
    )
    .unwrap();
    assert_eq!(data, derived);
    let pads = geometry.sc_geom.pad_layout(3);
    let relations = crate::runtime::sumcheck_v1::symbolic::verify(&proof, data, &f).unwrap();
    let independent_relations =
        crate::runtime::sumcheck_v1::symbolic::verify(&proof, derived, &f).unwrap();
    let (prover_a, prover_b) =
        crate::runtime::zk_v1::constraint_compiler::compile(&relations, &pads, &public, &f)
            .unwrap();
    let (a, b) = crate::runtime::zk_v1::constraint_compiler::compile(
        &independent_relations,
        &pads,
        &public,
        &f,
    )
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
        &crate::runtime::zk_v1::common::DEFAULT_STATEMENT_HASH,
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
        let mut verifier = crate::runtime::ligero::LigeroVerifier::new(&mut independent, &param);
        verifier
            .verify(
                &b,
                &actual.com,
                &actual.com_proof,
                &a,
                &crate::runtime::zk_v1::common::DEFAULT_STATEMENT_HASH,
                &committed.lqc,
                &interpolation,
                &f,
            )
            .unwrap();
    }
    assert_eq!(actual_state, numerical.bytes(32));
    assert_eq!(actual_state, independent.bytes(32));
}
