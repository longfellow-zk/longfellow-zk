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

use crate::{
    compile::{
        algebra::p256::P256Field as CompileP256,
        logic::{Logic, LogicIO},
    },
    core::proto::{
        reader::CircuitReader, v2::Circuit, writer::CircuitWriter, FieldID, SerializableField,
    },
    runtime::{
        algebra::{
            field::{RuntimeField, SupportsU64Conversions},
            p256::P256Field as RuntimeP256,
            AlgebraicField,
        },
        random::{RandomEngine, Transcript},
        sumcheck_v2::{eval_circuit, prove, verifier::verify, RoundPoly, SumcheckProof},
    },
};

fn zero_proof<const W: usize, F: SerializableField + RuntimeField<W>>(
    circ: &Circuit<F>,
    f: &F,
) -> SumcheckProof<W, F> {
    use crate::runtime::proto::sumcheck_v2::LayerProof;
    SumcheckProof {
        layers: circ
            .raw
            .layers
            .iter()
            .map(|layer| LayerProof {
                rounds: vec![
                    RoundPoly {
                        coefficients: [f.zero(), f.zero()]
                    };
                    layer.logw()
                ],
                claims: [f.zero(), f.zero()],
            })
            .collect(),
    }
}

#[test]
fn single_hand_rejects_a_false_internal_assertion() {
    use crate::{
        core::proto::{circuit::RawCircuit, Layer, TermDelta},
        runtime::proto::sumcheck_v2::LayerProof,
    };
    let f = RuntimeP256::new();
    let circuit = crate::core::proto::circuit::Circuit {
        id: [0; 32],
        raw: RawCircuit {
            ninput: 1,
            npublic_input: 0,
            noutput: 1,
            logv: 0,
            subfield_boundary: 0,
            constants: vec![f.zero()],
            layers: vec![Layer::new_compressed(
                1,
                0,
                vec![vec![TermDelta {
                    g: 0,
                    h: [0, 0],
                    k_index: 0,
                }]],
                vec![0],
            )],
        },
    };
    let circuit = crate::core::proto::v2::quadratic_fixture(circuit, &f);
    let pad = zero_proof(&circuit, &f);
    // With zero rounds the product check accepts A=1, B=0. The public
    // contraction of the assertion must still make the final input claim fail.
    let forged = SumcheckProof {
        layers: vec![LayerProof {
            rounds: vec![],
            claims: [f.one(), f.zero()],
        }],
    };
    assert!(verify(
        vec![f.one()],
        &pad,
        &circuit,
        &forged,
        &mut Transcript::new(b"false-assertion"),
        &f
    )
    .is_err());
    assert!(eval_circuit(vec![f.one()], &circuit, &f).is_err());
    let valid = zero_proof(&circuit, &f);
    verify(
        vec![f.zero()],
        &pad,
        &circuit,
        &valid,
        &mut Transcript::new(b"false-assertion"),
        &f,
    )
    .unwrap();
}

#[test]
fn test_sumcheck_prover_verifier_end_to_end() {
    let fc = CompileP256::new();
    let (circ_comp, _, _) = crate::compile::compiler::compile_v2(&fc, |iologic| {
        let x = iologic.input(1);
        let y = iologic.input(2);
        let z = iologic.mul(&x, &y);
        (iologic.assert0("assert_z", &z), 1, 0)
    });

    let f = RuntimeP256::new();
    let writer = CircuitWriter::new(&fc, FieldID::P256);
    let bytes = writer.to_bytes_lfc3(&circ_comp);
    let reader = CircuitReader::new(&f, FieldID::P256);
    let (circ, _) = reader
        .from_bytes_lfc3(&bytes, true)
        .expect("Circuit conversion to runtime field failed");

    // Witness where x = 1, y = 0 => z = 1 * 0 = 0 (satisfies assert0)
    let mut w0 = vec![f.zero(); circ.raw.ninput];
    w0[0] = f.one();
    w0[1] = f.zero();

    let in_layers = eval_circuit(w0.clone(), &circ, &f).unwrap();

    let mut transcript = Transcript::new(b"test_sumcheck");
    let pad = zero_proof(&circ, &f);
    let (proof, _) = prove(in_layers, &pad, &circ, &mut transcript, &f);

    let mut verifier_transcript = Transcript::new(b"test_sumcheck");
    let verify_result = verify(
        w0.clone(),
        &pad,
        &circ,
        &proof,
        &mut verifier_transcript,
        &f,
    );

    assert!(
        verify_result.is_ok(),
        "Verification failed: {:?}",
        verify_result.err()
    );

    let buf_prover = transcript.bytes(256);
    let buf_verifier = verifier_transcript.bytes(256);
    assert_eq!(
        buf_prover, buf_verifier,
        "Prover and verifier transcripts differ!"
    );
}

#[test]
fn test_sumcheck_prover_verifier_with_nonzero_pad() {
    let fc = CompileP256::new();
    let (circ_comp, _, _) = crate::compile::compiler::compile_v2(&fc, |iologic| {
        let x = iologic.input(1);
        let y = iologic.input(2);
        let z = iologic.mul(&x, &y);
        (iologic.assert0("assert_z", &z), 1, 0)
    });

    let f = RuntimeP256::new();
    let writer = CircuitWriter::new(&fc, FieldID::P256);
    let bytes = writer.to_bytes_lfc3(&circ_comp);
    let reader = CircuitReader::new(&f, FieldID::P256);
    let (circ, _) = reader
        .from_bytes_lfc3(&bytes, true)
        .expect("Circuit conversion to runtime field failed");

    let mut w_pad = vec![f.zero(); circ.raw.ninput];
    w_pad[1] = f.u64_to_element(5);

    let in_layers_pad = eval_circuit(w_pad, &circ, &f).unwrap();
    let zero_pad = zero_proof(&circ, &f);
    let mut transcript_pad = Transcript::new(b"test_sumcheck");
    let (pad, _) = prove(in_layers_pad, &zero_pad, &circ, &mut transcript_pad, &f);

    // The actual unpadded witness has x=0, y=0.
    let w0 = vec![f.zero(); circ.raw.ninput];
    let in_layers = eval_circuit(w0.clone(), &circ, &f).unwrap();

    let mut transcript = Transcript::new(b"test_sumcheck");
    let (proof, _) = prove(in_layers, &pad, &circ, &mut transcript, &f);

    let mut verifier_transcript = Transcript::new(b"test_sumcheck");
    let verify_result = verify(
        w0.clone(),
        &pad,
        &circ,
        &proof,
        &mut verifier_transcript,
        &f,
    );

    assert!(
        verify_result.is_ok(),
        "Verification failed: {:?}",
        verify_result.err()
    );

    let buf_prover = transcript.bytes(256);
    let buf_verifier = verifier_transcript.bytes(256);
    assert_eq!(
        buf_prover, buf_verifier,
        "Prover and verifier transcripts differ!"
    );
}

#[test]
fn test_sumcheck_multi_layer() {
    let fc = CompileP256::new();
    let (circ_comp, _, _) = crate::compile::compiler::compile_v2(&fc, |iologic| {
        let mut x = iologic.input(1);
        let y = iologic.input(2);
        for _ in 0..6 {
            let sum = iologic.add(&x, &y);
            x = iologic.mul(&sum, &x);
        }
        (iologic.assert0("assert_x", &x), 1, 0)
    });
    let f = RuntimeP256::new();
    let writer = CircuitWriter::new(&fc, FieldID::P256);
    let bytes = writer.to_bytes_lfc3(&circ_comp);
    let reader = CircuitReader::new(&f, FieldID::P256);
    let (circ, _) = reader
        .from_bytes_lfc3(&bytes, true)
        .expect("Circuit conversion to runtime field failed");
    assert!(
        circ.raw.layers.len() > 1,
        "Circuit must have multiple layers"
    );

    let mut w0 = vec![f.zero(); circ.raw.ninput];
    w0[1] = f.u64_to_element(12345);

    let in_layers = eval_circuit(w0.clone(), &circ, &f).unwrap();
    let mut transcript_prover = Transcript::new(b"test_multi_layer");
    let pad = zero_proof(&circ, &f);
    let (proof, _) = prove(in_layers, &pad, &circ, &mut transcript_prover, &f);

    let mut transcript_verifier = Transcript::new(b"test_multi_layer");
    let verify_result = verify(
        w0.clone(),
        &pad,
        &circ,
        &proof,
        &mut transcript_verifier,
        &f,
    );

    assert!(
        verify_result.is_ok(),
        "Verification failed: {:?}",
        verify_result.err()
    );
}

#[test]
fn test_sumcheck_core_single_hand_permutations() {
    use crate::{
        core::proto::v2::{compute_id, Stream},
        runtime::{
            proto::sumcheck_v2::SumcheckProofGeometry,
            sumcheck_v2::{prove_core, verifier::verify_core},
        },
    };

    let fc = CompileP256::new();
    let (compiled, _, _) = crate::compile::compiler::compile_v2(&fc, |logic| {
        let mut x = logic.input(1);
        let y = logic.input(2);
        for _ in 0..6 {
            let sum = logic.add(&x, &y);
            x = logic.mul(&sum, &x);
        }
        (logic.assert0("x", &x), 1, 0)
    });
    let bytes = CircuitWriter::new(&fc, FieldID::P256).to_bytes_lfc3(&compiled);
    let f = RuntimeP256::new();
    let reader = CircuitReader::new(&f, FieldID::P256);
    let writer = CircuitWriter::new(&f, FieldID::P256);

    let mut expected = None;
    let mut ids = Vec::new();
    for layout in 0..4 {
        let (mut circuit, _) = reader.from_bytes_lfc3(&bytes, true).unwrap();
        for layer in &mut circuit.raw.layers {
            macro_rules! reorder {
                ($($name:ident:$ty:ty),+ $(,)?) => {$(
                    let mut terms = Vec::new();
                    layer.$name.for_each(|t| terms.push(t));
                    match layout { 0 => (), 1 => terms.sort_by_key(|t| format!("{t:?}")), 2 => terms.reverse(), _ => { for chunk in terms.chunks_mut(3) { chunk.reverse(); } } }
                    layer.$name = Stream::<$ty>::from_terms(terms);
                )+};
            }
            use crate::core::proto::v2::{
                Constant, ConstantCoordinates, Linear, LinearCoordinates, Quadratic,
                QuadraticCoordinates,
            };
            reorder!(quadratic:Quadratic, quadratic_one:QuadraticCoordinates, quadratic_minus_one:QuadraticCoordinates, quadratic_assertions:QuadraticCoordinates,
                linear:Linear, linear_one:LinearCoordinates, linear_minus_one:LinearCoordinates, linear_assertions:LinearCoordinates,
                constant:Constant, constant_one:ConstantCoordinates, constant_minus_one:ConstantCoordinates);
        }
        circuit.id = compute_id(&f, &circuit.raw, circuit.coefficient_classes);
        ids.push(circuit.id);
        let segmented = crate::compile::compiler::segment_circuit_v2(&f, &circuit);
        let encoded = writer.to_bytes_lfc3(&segmented);
        let (decoded, tail) = reader.from_bytes_lfc3(&encoded, true).unwrap();
        circuit = decoded;
        assert!(tail.is_empty());
        let mut inputs = vec![f.zero(); circuit.raw.ninput];
        inputs[1] = f.u64_to_element(12345);
        let w_layers = eval_circuit(inputs.clone(), &circuit, &f).unwrap();
        let pad = zero_proof(&circuit, &f);
        // Deliberately hold challenges fixed by calling the core, after the
        // order-sensitive circuit-ID statement step. Full prove/verify binds IDs.
        let mut pt = Transcript::new(b"fixed-layout-comparison");
        let (proof, constraints) = prove_core(w_layers, &pad, &circuit, &mut pt, &f);
        let mut verifier_transcript = Transcript::new(b"fixed-layout-comparison");
        let derived = crate::runtime::sumcheck_v2::derive_constraints(
            &circuit,
            &proof,
            &mut verifier_transcript,
            &f,
        )
        .unwrap();
        assert_eq!(constraints, derived);
        let mut vt = Transcript::new(b"fixed-layout-comparison");
        verify_core(inputs, &pad, &circuit, &proof, &mut vt, &f).unwrap();
        let transcript = pt.bytes(64);
        assert_eq!(transcript, vt.bytes(64));
        assert_eq!(transcript, verifier_transcript.bytes(64));
        let geometry = SumcheckProofGeometry {
            logw_layers: circuit.raw.layers.iter().map(|l| l.logw()).collect(),
        };
        let result = (proof.write(&geometry, &f).unwrap(), constraints, transcript);
        if let Some(reference) = &expected {
            assert_eq!(&result, reference);
        } else {
            expected = Some(result);
        }
    }

    assert!(
        ids.iter().any(|id| id != &ids[0]),
        "layouts must actually differ"
    );
}
