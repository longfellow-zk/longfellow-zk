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
            v1::{compute_id, Circuit, Layer, RawCircuit, TermDelta},
            v2::quadratic_fixture,
        },
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, packing::binary::Binary128Extension,
            range_interpolation::BinaryInterpolatorFactory,
        },
        random::{DeterministicRng, RandomEngine},
        v2::{
            dual_packing::verifier::reduce,
            polygero::LinearStatement,
            proto::polygero::PolygeroConfig,
            zk::{
                constraint_compiler,
                joint::{JointParam, SelectedField},
                packing_commitment::PackingCommitment,
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
    let circuit = quadratic_fixture(
        Circuit {
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
    let circuit = quadratic_fixture(
        Circuit {
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
        &context,
    )
    .unwrap();
    let public = vec![true];
    let witness = vec![false, false, true];
    let seed = b"longfellow-v2/numerical-symbolic-equivalence";
    let statement = prover.statement(seed, &public).unwrap();

    // Reject a wrong witness length before sampling private masks.
    let mut rejected_rng = DeterministicRng::new(42);
    assert!(matches!(
        prover.commit([].to_vec(), &statement, &context, &mut rejected_rng),
        Err(error) if error == "witness length mismatch"
    ));
    assert_eq!(rejected_rng.bytes(32), DeterministicRng::new(42).bytes(32));
    // No statement, and so no transcript, for the wrong inputs.
    assert!(matches!(
        prover.statement(seed, &[]),
        Err(error) if error == "public inputs length mismatch"
    ));

    // Identical, independently sampled commitments let each single-use state
    // produce exactly one response, while exposing the same pads to this test.
    let committed = prover
        .commit(
            witness.to_vec(),
            &statement,
            &context,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
    let mut reference = prover
        .commit(
            witness.to_vec(),
            &statement,
            &context,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
    assert_eq!(committed.commitment, reference.commitment);
    let geometry = statement.geometry.clone();
    let (actual, mut actual_ts) = prover.prove(committed, &context).unwrap();

    let independent_param = JointParam::new((
        SelectedField::new(
            prover.participant.backend.layout.witness_count,
            geometry.config(),
            &domain,
        )
        .unwrap(),
        (),
    ))
    .unwrap();
    // The verifier's transcript opens with the same statement.
    let mut independent_verifier = independent_param.receive(
        &reference.commitment,
        (reference.fingerprints.clone(), ()),
        Transcript::new(&statement),
    );
    let mut numerical = reference.joint.transcript();
    let mut independent = independent_verifier.transcript();
    let public_elements: Vec<_> = public
        .iter()
        .map(|bit| if *bit { f.one() } else { f.zero() })
        .collect();
    let mut inputs = public_elements.clone();
    inputs.extend(
        witness
            .iter()
            .map(|bit| if *bit { f.one() } else { f.zero() }),
    );
    let w_layers = sumcheck::eval_circuit(inputs, &prover.circuit, &f).unwrap();
    let (proof, constraints) = sumcheck::prove_core(
        w_layers,
        reference.state.pads.as_proof(),
        &prover.circuit,
        &mut numerical,
        &f,
    );
    let verifier_constraints =
        sumcheck::derive_constraints(&prover.circuit, &proof, &mut independent, &f).unwrap();
    assert_eq!(constraints, verifier_constraints);
    let mut different_execution = numerical.fork_for_test();
    different_execution.send_for_test(b"different sumcheck execution");
    let state = numerical.fork_for_test().bytes(32);
    assert_eq!(state, independent.fork_for_test().bytes(32));
    assert_ne!(state, different_execution.bytes(32));
    let layout = prover.participant.backend.layout.clone();
    let pads = geometry
        .circuit()
        .sumcheck()
        .pad_layout(layout.suffix_start);
    let source = constraint_compiler::compile_packed(
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
    let verifier_backend = PackingCommitment::new(f.clone(), layout, Binary128Extension).unwrap();
    let commitment = reference.commitment.clone();
    let (packing, native) = PackingCommitment::prove::<2>(
        &mut reference.joint.bound(&prover.participant.backend),
        reference.state.packing,
        source,
    )
    .unwrap();
    let joint = JointParam::new((prover.participant.participant(&context).unwrap(), ())).unwrap();
    let (com_proof, mut numerical) = reference.joint.finish(&joint, (native, ())).unwrap();
    let rows = reduce(
        &mut independent_verifier.bound(&verifier_backend.parameters),
        &verifier_source.claim,
        &packing,
    )
    .unwrap();
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
    let equations = (
        LinearStatement {
            a: verifier_a,
            b: verifier_b,
            session: independent_verifier.bound(&()).session(),
        },
        (),
    );
    let mut independent = independent_verifier
        .finish(equations, &actual.com_proof)
        .unwrap()
        .into_transcript();
    let state = actual_ts.bytes(32);
    assert_eq!(state, numerical.bytes(32));
    assert_eq!(state, independent.bytes(32));
}

/// `prove` takes a commitment state only from the participant that prepared
/// it: a state prepared for a circuit with another ID, but the same shape,
/// is rejected before any message.
#[test]
fn prove_rejects_a_state_of_another_participant() {
    let f = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let context = ZkContext::new(&domain);
    let raw = || RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one()],
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
    let fixture = || {
        let r = raw();
        quadratic_fixture(
            Circuit {
                id: compute_id(&f, &r),
                raw: r,
            },
            &f,
        )
    };
    let circuit = fixture();
    let mut id = circuit.id;
    id[0] ^= 1;
    let renamed = crate::core::proto::v2::Circuit::with_test_id(id, fixture().into_raw());
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let prover = ZkProver::new(circuit, config, &context).unwrap();
    let other = ZkProver::new(renamed, config, &context).unwrap();
    // x1 * x2 = 0: the witness satisfies the circuit, so only the check rejects.
    let (public, witness) = (vec![true], vec![false, true]);
    let statement = prover.statement(b"state", &public).unwrap();
    let other_statement = other.statement(b"state", &public).unwrap();
    let mut rng = DeterministicRng::new(5);
    let mut committed = prover
        .commit(witness.clone(), &statement, &context, &mut rng)
        .unwrap();
    let foreign = other
        .commit(witness, &other_statement, &context, &mut rng)
        .unwrap();
    let mut t = committed.joint.bound(&statement.part);
    let top = top_weights(&mut t).unwrap();
    let result = prove(&mut t, foreign.state, top, &VirtualInputs::none(), &context);
    assert_eq!(
        result.err().unwrap(),
        "commitment belongs to another participant"
    );
}
