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
    core::proto::v1::{compute_id, Layer, RawCircuit, TermDelta},
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory, AlgebraicField,
        },
        polygero::{PolygeroConfig, PolygeroParam, PolygeroVerifier},
        proto::zk_v2::product_constraints,
        random::{DeterministicRng, RandomEngine},
        zk_v2::{constraint_compiler, transcript::statement_digest, ZkContext},
    },
};

#[test]
fn evaluation_failures_do_not_disclose_witness_values() {
    use crate::core::algebra::SupportsU128Conversions;
    let f = Gf2_128Field::new();
    let raw = RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.zero()],
        layers: vec![Layer::new_compressed(
            3,
            2,
            vec![vec![TermDelta {
                g: 0,
                h: [1, 2],
                k_index: 0,
            }]],
            vec![0],
        )],
    };
    let circuit = crate::core::proto::v2::quadratic_fixture(
        crate::core::proto::v1::Circuit {
            id: compute_id(&f, &raw),
            raw,
        },
        &f,
    );
    for secret in [17, 0x12345678, 0xabcdef01] {
        let inputs = vec![
            f.one(),
            f.u128_to_element(secret),
            f.u128_to_element(secret + 1),
        ];
        let message = sumcheck_v2::eval_circuit(inputs, &circuit, &f).unwrap_err();
        assert_eq!(message, "Witness does not satisfy circuit constraints at layer 0: quadratic assertion not satisfied");
    }
}

#[test]
fn zk_prover_matches_numerical_prover_and_symbolic_verifier() {
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let context = ZkContext {
        f: &f,
        domain: &domain,
    };
    let raw = RawCircuit {
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
    };
    let circuit = crate::core::proto::v2::quadratic_fixture(
        crate::core::proto::v1::Circuit {
            id: compute_id(&f, &raw),
            raw,
        },
        &f,
    );
    let prover = ZkProver::new(
        circuit,
        PolygeroConfig {
            k: 16,
            s: 2,
            n: 128,
            t: 2,
        },
    );
    let public = vec![f.one()];
    let witness = vec![f.zero(), f.zero(), f.one()];
    let seed = b"longfellow-v2/numerical-symbolic-equivalence";

    // Input-shape errors must not consume random masks or transcript challenges.
    let mut rejected_ts = Transcript::new(seed);
    let mut original_ts = rejected_ts.clone();
    let mut rejected_rng = DeterministicRng::new(42);
    assert!(matches!(
        prover.commit(&[], &context, &mut rejected_ts, &mut rejected_rng),
        Err(error) if error == "witness length mismatch"
    ));
    assert_eq!(rejected_ts.bytes(32), original_ts.bytes(32));
    assert_eq!(rejected_rng.bytes(32), DeterministicRng::new(42).bytes(32));

    for (inputs, private, expected_error) in [
        (&[][..], witness.clone(), "public inputs length mismatch"),
        (public.as_slice(), vec![], "witness length mismatch"),
    ] {
        let mut transcript = Transcript::new(seed);
        let (committed, _) = prover
            .commit(
                &witness,
                &context,
                &mut transcript,
                &mut DeterministicRng::new(42),
            )
            .unwrap();
        let mut unchanged = transcript.clone();
        assert!(matches!(
            prover.prove(inputs, private, committed, &mut transcript, &context),
            Err(error) if error == expected_error
        ));
        assert_eq!(transcript.bytes(32), unchanged.bytes(32));
    }

    let mut actual_ts = Transcript::new(seed);
    let mut numerical = Transcript::new(seed);
    let mut independent = Transcript::new(seed);
    // Identical, independently sampled commitments let each single-use state
    // produce exactly one response, while exposing the same pads to this test.
    let (committed, geometry) = prover
        .commit(
            &witness,
            &context,
            &mut actual_ts,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
    let (reference, reference_geometry) = prover
        .commit(
            &witness,
            &context,
            &mut numerical,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
    assert_eq!(committed.commitment, reference.commitment);
    assert_eq!(geometry, reference_geometry);
    let actual = prover
        .prove(
            &public,
            witness.clone(),
            committed,
            &mut actual_ts,
            &context,
        )
        .unwrap();

    let independent_products = product_constraints(
        prover.circuit.raw.ninput - prover.circuit.raw.npublic_input,
        &geometry.sc_geom,
    );
    let independent_param = PolygeroParam::try_new(
        crate::runtime::zk_v2::witness_and_constraint_count(&prover.circuit).0,
        &independent_products,
        prover.config,
        &domain,
        &f,
    )
    .unwrap();
    let mut independent_verifier = PolygeroVerifier::new(independent_param);
    independent_verifier.receive_commitment(&reference.commitment, &mut independent);
    for transcript in [&mut numerical, &mut independent] {
        transcript.write_sumcheck_statement(&prover.circuit, &public, &f);
    }
    let mut inputs = public.clone();
    inputs.extend(witness);
    let w_layers = sumcheck_v2::eval_circuit(inputs, &prover.circuit, &f).unwrap();
    let (proof, constraints) = sumcheck_v2::prove_core(
        w_layers,
        &reference.pads,
        &prover.circuit,
        &mut numerical,
        &f,
    );
    let verifier_constraints =
        sumcheck_v2::derive_constraints(&prover.circuit, &proof, &mut independent, &f).unwrap();
    assert_eq!(constraints, verifier_constraints);
    let mut different_execution = numerical.clone();
    different_execution.write_bytes(b"different sumcheck execution");
    let statement = statement_digest(&mut numerical);
    let verifier_statement = statement_digest(&mut independent);
    assert_eq!(statement, verifier_statement);
    assert_ne!(statement, statement_digest(&mut different_execution));
    assert_ne!(statement.data, prover.circuit.id);
    let pads = geometry
        .sc_geom
        .pad_layout(prover.circuit.raw.ninput - public.len());
    let (a, b) = constraint_compiler::compile(&constraints, &pads, &public, &f).unwrap();
    let (verifier_a, verifier_b) =
        constraint_compiler::compile(&verifier_constraints, &pads, &public, &f).unwrap();
    assert_eq!(a, verifier_a);
    assert_eq!(b, verifier_b);
    let com_proof = reference
        .polygero
        .prove(&b, &mut numerical, &a, &statement, &domain, &f)
        .unwrap();
    let expected = ZkProof {
        com: reference.commitment,
        sumcheck_proof: proof,
        com_proof,
    };
    assert_eq!(
        actual.write(&geometry, &f).unwrap(),
        expected.write(&geometry, &f).unwrap()
    );
    independent_verifier
        .verify(
            &verifier_b,
            &actual.com,
            &actual.com_proof,
            &verifier_a,
            &verifier_statement,
            &mut independent,
            &domain,
            &f,
        )
        .unwrap();
    let state = actual_ts.bytes(32);
    assert_eq!(state, numerical.bytes(32));
    assert_eq!(state, independent.bytes(32));
}
