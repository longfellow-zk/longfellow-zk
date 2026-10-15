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

use compile_algebra::p256::P256Field as CompileP256;
use compile_logic::{Logic, LogicIO};
use core_proto::{
    circuit::Circuit, reader::CircuitReader, writer::CircuitWriter, FieldID, SerializableField,
};
use runtime_algebra::{
    field::{RuntimeField, SupportsU64Conversions},
    p256::P256Field as RuntimeP256,
    AlgebraicField,
};
use runtime_random::{RandomEngine, Transcript};
use runtime_sumcheck::{
    eval::eval_circuit, prover::prove, verifier::verify, LayerProof, Poly, QuadRoundPoly,
    SumcheckProof,
};

fn zero_proof<const W: usize, F: SerializableField + RuntimeField<W>>(
    circ: &Circuit<F>,
    f: &F,
) -> SumcheckProof<W, F> {
    let mut layers = Vec::new();
    for ly in 0..circ.raw.layers.len() {
        let clr = &circ.raw.layers[ly];
        let hp = [
            vec![Poly::<3, W, F>::zero(f).to_wire(); clr.logw()],
            vec![Poly::<3, W, F>::zero(f).to_wire(); clr.logw()],
        ];
        let claims = [f.zero(), f.zero()];
        layers.push(LayerProof { hp, claims });
    }
    SumcheckProof { layers }
}

#[test]
fn test_sumcheck_prover_verifier_end_to_end() {
    let fc = CompileP256::new();
    let (circ_comp, _, _) = compile_compiler::compile(&fc, |iologic| {
        let x = iologic.input(1);
        let y = iologic.input(2);
        let z = iologic.mul(&x, &y);
        (iologic.assert0("assert_z", &z), 1, 0)
    });

    let f = RuntimeP256::new();
    let writer = CircuitWriter::new(&fc, FieldID::P256);
    let bytes = writer.to_bytes_lfc2(&circ_comp);
    let reader = CircuitReader::new(&f, FieldID::P256);
    let (circ, _) = reader
        .from_bytes_lfc2(&bytes, true)
        .expect("Circuit conversion to runtime field failed");

    // Witness where x = 1, y = 0 => z = 1 * 0 = 0 (satisfies assert0)
    let mut w0 = vec![f.zero(); circ.raw.ninput];
    w0[0] = f.one();
    w0[1] = f.one();
    w0[2] = f.zero();

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
    let (circ_comp, _, _) = compile_compiler::compile(&fc, |iologic| {
        let x = iologic.input(1);
        let y = iologic.input(2);
        let z = iologic.mul(&x, &y);
        (iologic.assert0("assert_z", &z), 1, 0)
    });

    let f = RuntimeP256::new();
    let writer = CircuitWriter::new(&fc, FieldID::P256);
    let bytes = writer.to_bytes_lfc2(&circ_comp);
    let reader = CircuitReader::new(&f, FieldID::P256);
    let (circ, _) = reader
        .from_bytes_lfc2(&bytes, true)
        .expect("Circuit conversion to runtime field failed");

    let mut w_pad = vec![f.zero(); circ.raw.ninput];
    w_pad[0] = f.one();
    w_pad[2] = f.u64_to_element(5);

    let in_layers_pad = eval_circuit(w_pad, &circ, &f).unwrap();
    let zero_pad = zero_proof(&circ, &f);
    let mut transcript_pad = Transcript::new(b"test_sumcheck");
    let (pad, _) = prove(in_layers_pad, &zero_pad, &circ, &mut transcript_pad, &f);

    // The actual unpadded witness is where x=0, y=0. Position 0 is One.
    let mut w0 = vec![f.zero(); circ.raw.ninput];
    w0[0] = f.one();
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
    let (circ_comp, _, _) = compile_compiler::compile(&fc, |iologic| {
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
    let bytes = writer.to_bytes_lfc2(&circ_comp);
    let reader = CircuitReader::new(&f, FieldID::P256);
    let (circ, _) = reader
        .from_bytes_lfc2(&bytes, true)
        .expect("Circuit conversion to runtime field failed");
    assert!(
        circ.raw.layers.len() > 1,
        "Circuit must have multiple layers"
    );

    let mut w0 = vec![f.zero(); circ.raw.ninput];
    w0[0] = f.one();
    w0[1] = f.zero();
    w0[2] = f.u64_to_element(12345);

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
fn test_sumcheck_core_hand_major_permutations_and_round_major_morton() {
    use core_proto::{circuit::compute_id, Layer, TermDelta};
    use runtime_proto::sumcheck::SumcheckProofGeometry;
    use runtime_sumcheck::{prove_core_with_order, verify_core_with_order, SumcheckOrder};

    let fc = CompileP256::new();
    let (compiled, _, _) = compile_compiler::compile(&fc, |logic| {
        let mut x = logic.input(1);
        let y = logic.input(2);
        for _ in 0..6 {
            let sum = logic.add(&x, &y);
            x = logic.mul(&sum, &x);
        }
        (logic.assert0("x", &x), 1, 0)
    });
    let bytes = CircuitWriter::new(&fc, FieldID::P256).to_bytes_lfc2(&compiled);
    let f = RuntimeP256::new();
    let reader = CircuitReader::new(&f, FieldID::P256);
    let writer = CircuitWriter::new(&f, FieldID::P256);
    for order in [SumcheckOrder::HandMajor, SumcheckOrder::RoundMajor] {
        let mut expected = None;
        let mut ids = Vec::new();
        for layout in 0..4 {
            if order == SumcheckOrder::RoundMajor && layout != 1 {
                continue; // Round-major consumes only preordered Morton terms.
            }
            let (mut circuit, _) = reader.from_bytes(&bytes, true).unwrap();
            for layer in &mut circuit.raw.layers {
                let mut terms = layer.terms(&circuit.raw.constants);
                match layout {
                    0 => {}
                    1 => terms.sort_by_key(|t| {
                        let mut morton = 0u64;
                        for bit in 0..32 {
                            morton |= (((t.h0 >> bit) & 1) as u64) << (2 * bit);
                            morton |= (((t.h1 >> bit) & 1) as u64) << (2 * bit + 1);
                        }
                        (morton, t.g)
                    }),
                    2 => terms.reverse(),
                    _ => {
                        for chunk in terms.chunks_mut(3) {
                            chunk.reverse();
                        }
                    }
                }
                let mut previous = [0u32; 3];
                let deltas = terms
                    .iter()
                    .map(|t| {
                        let delta = TermDelta {
                            g: t.g.wrapping_sub(previous[0]),
                            h: [
                                t.h0.wrapping_sub(previous[1]),
                                t.h1.wrapping_sub(previous[2]),
                            ],
                            k_index: circuit
                                .raw
                                .constants
                                .iter()
                                .position(|k| k == &t.k)
                                .unwrap() as u32,
                        };
                        previous = [t.g, t.h0, t.h1];
                        delta
                    })
                    .collect();
                *layer = Layer::new_compressed(layer.nw(), layer.logw(), vec![deltas], vec![0]);
            }
            circuit.id = compute_id(&f, &circuit.raw);
            ids.push(circuit.id);
            let segmented = compile_compiler::segment_circuit(&f, &circuit);
            let encoded = writer.to_bytes_lfc2(&segmented);
            let (decoded, tail) = reader.from_bytes(&encoded, true).unwrap();
            circuit = decoded;
            assert!(tail.is_empty());
            let mut inputs = vec![f.zero(); circuit.raw.ninput];
            inputs[0] = f.one();
            inputs[2] = f.u64_to_element(12345);
            let in_layers = eval_circuit(inputs.clone(), &circuit, &f).unwrap();
            let pad = zero_proof(&circuit, &f);
            // Deliberately hold challenges fixed by calling the core, after the
            // order-sensitive circuit-ID statement step. Full prove/verify binds IDs.
            let mut pt = Transcript::new(b"fixed-layout-comparison");
            let (proof, aux) = prove_core_with_order(in_layers, &pad, &circuit, &mut pt, &f, order);
            let mut vt = Transcript::new(b"fixed-layout-comparison");
            verify_core_with_order(inputs, &pad, &circuit, &proof, &mut vt, &f, order).unwrap();
            let transcript = pt.bytes(64);
            assert_eq!(transcript, vt.bytes(64));
            let geometry = SumcheckProofGeometry {
                logw_layers: circuit.raw.layers.iter().map(Layer::logw).collect(),
            };
            let result = (
                proof.write(&geometry, &f).unwrap(),
                aux.bound_quad,
                transcript,
            );
            if let Some(reference) = &expected {
                assert_eq!(&result, reference);
            } else {
                expected = Some(result);
            }
        }
        if order == SumcheckOrder::HandMajor {
            assert!(
                ids.iter().any(|id| id != &ids[0]),
                "layouts must actually differ"
            );
        }
    }
}
