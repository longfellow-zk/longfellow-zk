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
        random::{DeterministicRng, RandomEngine},
        v2::{
            polygero::{LinearStatement, PolygeroConfig},
            zk::{
                constraint_compiler,
                joint::{JointParam, SelectedField},
                ZkContext,
            },
        },
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
        let message = sumcheck::eval_circuit(inputs, &circuit, &f).unwrap_err();
        assert_eq!(message, "Witness does not satisfy circuit constraints at layer 0: quadratic assertion not satisfied");
    }
}

#[test]
fn zk_prover_matches_numerical_prover_and_symbolic_verifier() {
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let context = ZkContext::new(&domain);
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
    let public = vec![true];
    let witness = vec![false, false, true];
    let seed = b"longfellow-v2/numerical-symbolic-equivalence";

    // Reject a wrong witness length before sampling private masks.
    let rejected_ts = Transcript::new(seed);
    let mut rejected_rng = DeterministicRng::new(42);
    assert!(matches!(
        prover.commit([].to_vec(), &context, rejected_ts, &mut rejected_rng),
        Err(error) if error == "witness length mismatch"
    ));
    assert_eq!(rejected_rng.bytes(32), DeterministicRng::new(42).bytes(32));

    {
        let inputs: &[bool] = &[];
        let transcript = Transcript::new(seed);
        let (mut committed, _) = prover
            .commit(
                witness.to_vec(),
                &context,
                transcript,
                &mut DeterministicRng::new(42),
            )
            .unwrap();
        let mut transcript = committed.joint.transcript();
        let mut unchanged = transcript.fork_for_test();
        assert!(matches!(
            committed.participant.prove(
                &[&prover.circuit],
                inputs,
                committed.state,
                &VirtualInputs::none(),
                &mut transcript,
                &context
            ),
            Err(error) if error == "public inputs length mismatch"
        ));
        assert_eq!(transcript.bytes(32), unchanged.bytes(32));
    }

    let actual_ts = Transcript::new(seed);
    let numerical = Transcript::new(seed);
    let mut independent = Transcript::new(seed);
    // Identical, independently sampled commitments let each single-use state
    // produce exactly one response, while exposing the same pads to this test.
    let (committed, geometry) = prover
        .commit(
            witness.to_vec(),
            &context,
            actual_ts,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
    let (mut reference, reference_geometry) = prover
        .commit(
            witness.to_vec(),
            &context,
            numerical,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
    assert_eq!(committed.commitment, reference.commitment);
    assert_eq!(geometry, reference_geometry);
    let (actual, mut actual_ts) = prover.prove(&public, committed, &context).unwrap();

    let independent_param = JointParam::new((
        SelectedField::new(
            reference.participant.backend.layout.witness_count,
            prover.config,
            &domain,
            crate::runtime::algebra::PackingField::packing_id(&f),
        )
        .unwrap(),
        (),
    ))
    .unwrap();
    reference
        .participant
        .backend
        .absorb(&mut independent.borrow(), &prover.circuit.id);
    independent.absorb(|w| {
        w.write_bytes(b"layered-sumcheck/commitment-layout/v1");
        w.write_bytes(&0u64.to_le_bytes());
    }); // No additional circuits.
    independent.absorb(|w| {
        w.write_bytes(&(geometry.circuit.sc_geom.logw_layers.len() as u64).to_le_bytes())
    });
    for &width in &geometry.circuit.sc_geom.logw_layers {
        independent.absorb(|w| w.write_bytes(&(width as u64).to_le_bytes()));
    }
    let mut independent_verifier = independent_param.receive(
        &reference.commitment,
        (reference.fingerprints.clone(), ()),
        independent,
    );
    let mut numerical = reference.joint.transcript();
    let mut independent = independent_verifier.transcript();
    let public_elements: Vec<_> = public
        .iter()
        .map(|bit| if *bit { f.one() } else { f.zero() })
        .collect();
    numerical.write_sumcheck_statement(&prover.circuit, &public_elements, &f);
    independent.write_sumcheck_statement(&prover.circuit, &public_elements, &f);
    let mut inputs = public_elements.clone();
    inputs.extend(
        witness
            .iter()
            .map(|bit| if *bit { f.one() } else { f.zero() }),
    );
    let w_layers = sumcheck::eval_circuit(inputs, &prover.circuit, &f).unwrap();
    let (proof, constraints) = sumcheck::prove_core(
        w_layers,
        &reference.state.pads,
        &prover.circuit,
        &mut numerical,
        &f,
    );
    let verifier_constraints =
        sumcheck::derive_constraints(&prover.circuit, &proof, &mut independent, &f).unwrap();
    assert_eq!(constraints, verifier_constraints);
    let mut different_execution = numerical.fork_for_test();
    different_execution.absorb(|w| w.write_bytes(b"different sumcheck execution"));
    let state = numerical.fork_for_test().bytes(32);
    assert_eq!(state, independent.fork_for_test().bytes(32));
    assert_ne!(state, different_execution.bytes(32));
    let layout = reference.participant.backend.layout.clone();
    let pads = geometry.circuit.sc_geom.pad_layout(layout.suffix_start);
    let source =
        constraint_compiler::compile_packed(
            constraints,
            &pads,
            &public_elements,
            &layout,
            &crate::runtime::v2::zk::VirtualInputs::none(),
            &f,
        )
            .unwrap();
    let verifier_source = constraint_compiler::compile_packed(
        verifier_constraints,
        &pads,
        &public_elements,
        &layout,
        &crate::runtime::v2::zk::VirtualInputs::none(),
        &f,
    )
    .unwrap();
    assert_eq!(source.claim, verifier_source.claim);
    assert_eq!(source.a, verifier_source.a);
    assert_eq!(source.b, verifier_source.b);
    let verifier_backend = crate::runtime::v2::zk::packing_commitment::PackingCommitment::new(
        f.clone(),
        layout,
        crate::runtime::algebra::packing::binary::Binary128Extension,
    )
    .unwrap();
    let commitment = reference.commitment.clone();
    let (packing, native) = reference
        .participant
        .backend
        .prove::<2>(
            reference.state.packing,
            source,
            &prover.circuit.id,
            &mut numerical,
        )
        .unwrap();
    let joint =
        JointParam::new((reference.participant.participant(&context).unwrap(), ())).unwrap();
    let (com_proof, mut numerical) = reference.joint.prove(&joint, (native, ())).unwrap();
    let rows = crate::runtime::v2::dual_packing::verifier::reduce(
        &verifier_backend.parameters,
        &verifier_source.claim,
        &packing,
        &prover.circuit.id,
        &mut independent,
    )
    .unwrap();
    let verifier_statement = crate::runtime::v2::proto::Digest {
        data: prover.circuit.id,
    };
    let (verifier_a, verifier_b) = verifier_backend
        .append_equations::<2>(verifier_source, &rows)
        .unwrap();
    let expected = ZkProof {
        com: commitment,
        fingerprints: reference.fingerprints,
        sumcheck_proof: proof,
        packing,
        com_proof,
    };
    assert_eq!(
        actual
            .write(&geometry, &f, numerical.fork_for_test())
            .unwrap()
            .into_bytes(),
        expected
            .write(&geometry, &f, numerical.fork_for_test())
            .unwrap()
            .into_bytes()
    );
    let mut independent = independent_verifier
        .authenticate(
            &actual.com_proof,
            (
                LinearStatement {
                    a: verifier_a,
                    b: verifier_b,
                    digest: verifier_statement,
                },
                (),
            ),
        )
        .unwrap()
        .into_transcript();
    let state = actual_ts.bytes(32);
    assert_eq!(state, numerical.bytes(32));
    assert_eq!(state, independent.bytes(32));
}
