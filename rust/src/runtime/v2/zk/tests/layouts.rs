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
    core::{
        algebra::{AlgebraicField, SerializableField},
        proto::{
            v1::{compare_term, Circuit, Layer, RawCircuit, Term, TermDelta},
            v2::quadratic_fixture,
        },
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory, RuntimeField,
        },
        random::{PrivateRandom, RandomEngine, Sealed},
        v2::{
            proto::{polygero::PolygeroConfig, zk::ZkProof},
            sumcheck::eval_circuit,
            transcript::{Transcript, SEAL_BYTES},
            zk::{ZkProver, ZkVerifier},
        },
    },
};

struct SimpleRng {
    state: u64,
}

impl RandomEngine for SimpleRng {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut buf = Vec::with_capacity(len);
        for _ in 0..len {
            self.state = self
                .state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            buf.push((self.state >> 32) as u8);
        }
        buf
    }
}
impl Sealed for SimpleRng {}
impl PrivateRandom for SimpleRng {}

#[allow(clippy::too_many_arguments)]
fn make_raw_circuit<const W: usize, F: RuntimeField<W> + SerializableField>(
    f: &F,
    ninput: usize,
    npublic_input: usize,
    noutput: usize,
    logv: usize,
    layer_ninputs: &[usize],
    layer_logws: &[usize],
    layers_terms: Vec<Vec<Term<F>>>,
) -> RawCircuit<F> {
    let mut constants = Vec::new();
    let mut layers = Vec::new();
    let mut constant_to_idx = std::collections::HashMap::new();

    for (i, terms) in layers_terms.into_iter().enumerate() {
        let mut terms_sorted = terms;
        terms_sorted.sort_by(|a, b| compare_term(f, a, b));

        let mut deltas = Vec::new();
        let mut delta_to_idx = std::collections::HashMap::new();
        let mut delta_segment = Vec::with_capacity(terms_sorted.len());
        let mut prev_g = 0u32;
        let mut prev_h0 = 0u32;
        let mut prev_h1 = 0u32;

        for term in terms_sorted {
            let key = f.to_bytes(&term.k);
            let k_index = *constant_to_idx.entry(key).or_insert_with(|| {
                let idx = constants.len() as u32;
                constants.push(term.k.clone());
                idx
            });

            let dg = term.g.wrapping_sub(prev_g);
            let dh0 = term.h0.wrapping_sub(prev_h0);
            let dh1 = term.h1.wrapping_sub(prev_h1);

            let d = TermDelta {
                g: dg,
                h: [dh0, dh1],
                k_index,
            };

            let idx = *delta_to_idx.entry(d).or_insert_with(|| {
                let idx = deltas.len() as u32;
                deltas.push(d);
                idx
            });

            delta_segment.push(idx);

            prev_g = term.g;
            prev_h0 = term.h0;
            prev_h1 = term.h1;
        }

        let unrolled_deltas: Vec<crate::core::proto::v1::TermDelta> = delta_segment
            .iter()
            .map(|&idx| deltas[idx as usize])
            .collect();

        layers.push(Layer::new_compressed(
            layer_ninputs[i],
            layer_logws[i],
            vec![unrolled_deltas],
            vec![0],
        ));
    }

    RawCircuit {
        ninput,
        npublic_input,
        noutput,
        logv,
        subfield_boundary: 0,
        constants,
        layers,
    }
}

#[test]
fn test_zk_prover_verifier_end_to_end() {
    let f = Gf2_128Field::new();

    // 1. Manually build a simple 1-layer circuit
    let term = Term {
        k: f.one(),
        g: 0,
        h0: 0,
        h1: 1,
    };
    let raw = make_raw_circuit(&f, 2, 0, 1, 0, &[2], &[1], vec![vec![term]]);
    let circ = quadratic_fixture(Circuit { raw, id: [0u8; 32] }, &f);

    // 2. Setup inputs
    let w0 = [true, false];

    // 3. Prover commit
    let make_interpolator = BinaryInterpolatorFactory::full_field(&f);

    let mut rng = SimpleRng { state: 42 };

    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    // 4. Prover commit and prove
    let prover_inst = ZkProver::new(circ, config, &make_interpolator).unwrap();
    let npublic = prover_inst.circuit.raw.npublic_input;
    let (encoded, geom) = super::prove_standalone(
        &prover_inst,
        b"test_zk",
        &w0[..npublic],
        w0[npublic..].to_vec(),
        &make_interpolator,
        &mut rng,
    )
    .expect("Failed to prove");
    // 5. Deserialize the sealed proof
    let serialized = encoded.into_bytes();
    let verifier = ZkVerifier::new(prover_inst.circuit, config, &make_interpolator).unwrap();
    assert_eq!(verifier.geometry(), geom);
    let deserialized =
        super::read_standalone(&verifier, b"test_zk", &w0[..npublic], &serialized, &f)
            .expect("Failed to deserialize ZkProof");
    // The body round-trips: encoding the decoded proof gives every byte
    // before the seal.
    let body = serialized.len() - SEAL_BYTES;
    let reencoded = deserialized
        .write(&geom, &f, Transcript::for_test(b"re-encode"))
        .unwrap()
        .into_bytes();
    assert_eq!(reencoded[..body], serialized[..body]);

    // 6. Verifier verify
    let verify_res = super::reduce_standalone(
        &verifier,
        b"test_zk",
        &w0[..verifier.public_input_count()],
        &deserialized,
        &make_interpolator,
    );

    assert!(
        verify_res.is_ok(),
        "ZK Verification failed: {:?}",
        verify_res.err()
    );
}

#[test]
fn test_zk_supported_layouts_multibit_roundtrip_and_tampering() {
    use crate::core::{
        algebra::FieldID,
        proto::v1::{compute_id, CircuitReader, CircuitWriter},
    };

    let f = Gf2_128Field::new();
    let interpolation = BinaryInterpolatorFactory::full_field(&f);
    // A non-power-of-two width exercises several sumcheck rounds and input pairs
    // (0,3)/(2,2), whose Morton and lexicographic orders differ.
    let inputs: Vec<_> = (1..=7).map(|v| v % 3 != 0).collect();
    let mut terms = Vec::new();
    let mut sum = f.zero();
    for h0 in 0..7 {
        for h1 in h0..7 {
            f.fma(
                &mut sum,
                &if inputs[h0] { f.one() } else { f.zero() },
                &if inputs[h1] { f.one() } else { f.zero() },
            );
            terms.push(Term {
                h0: h0 as u32,
                h1: h1 as u32,
                g: 0,
                k: f.one(),
            });
        }
    }
    if !f.is_zero(&sum) {
        terms.push(Term {
            h0: 0,
            h1: 0,
            g: 0,
            k: f.neg(&sum),
        });
    }
    // Two outputs deliberately repeat input pairs. In output-major order these
    // pairs are nonadjacent. Every stored traversal below must work.
    terms.extend(terms.clone().into_iter().map(|mut t| {
        t.g = 1;
        t
    }));

    for layout in 0..5 {
        let mut raw = make_raw_circuit(&f, 7, 1, 2, 1, &[7], &[3], vec![terms.clone()]);
        let mut ordered = raw.layers[0].terms(&raw.constants);
        match layout {
            0 => {}
            1 => ordered.sort_by_key(|t| (std::cmp::Reverse(t.g), std::cmp::Reverse(t.h1), t.h0)),
            2 => ordered.reverse(),
            4 => ordered.sort_by_key(|t| {
                // Explicit legacy Morton traversal, with h0 as the low bit.
                let mut morton = 0u64;
                for bit in 0..32 {
                    morton |= (((t.h0 >> bit) & 1) as u64) << (2 * bit);
                    morton |= (((t.h1 >> bit) & 1) as u64) << (2 * bit + 1);
                }
                (morton, t.g)
            }),
            _ => {
                // Neither input nor output coordinates are globally monotone.
                let mid = ordered.len() / 3;
                ordered.rotate_left(mid);
                for chunk in ordered.chunks_mut(3) {
                    chunk.reverse();
                }
            }
        }
        let mut previous = [0u32; 3];
        let deltas = ordered
            .iter()
            .map(|t| {
                let delta = TermDelta {
                    g: t.g.wrapping_sub(previous[0]),
                    h: [
                        t.h0.wrapping_sub(previous[1]),
                        t.h1.wrapping_sub(previous[2]),
                    ],
                    k_index: raw.constants.iter().position(|k| k == &t.k).unwrap() as u32,
                };
                previous = [t.g, t.h0, t.h1];
                delta
            })
            .collect();
        raw.layers[0] = Layer::new_compressed(7, 3, vec![deltas], vec![0]);
        let circuit = Circuit {
            id: compute_id(&f, &raw),
            raw,
        };
        let writer = CircuitWriter::new(&f, FieldID::Gf2_128);
        let config = PolygeroConfig {
            k: 16,
            s: 2,
            n: 128,
            t: 4,
        };

        const LABEL: &[u8] = b"lexicographic-zk";
        // All-zero witnesses exercise a zero final claim.
        let zero_inputs = vec![false; inputs.len()];
        for witness_inputs in [&inputs, &zero_inputs] {
            let serializations = vec![
                writer.to_bytes_lfc1(&circuit),
                writer.to_bytes_lfc2(&circuit),
            ];
            let mut expected_proof = None;
            for bytes in serializations {
                let (decoded, tail) = CircuitReader::new(&f, FieldID::Gf2_128)
                    .from_bytes(&bytes, true)
                    .unwrap();
                assert!(tail.is_empty());
                assert_eq!(decoded.id, circuit.id);
                assert_eq!(decoded.raw.layers[0].terms(&decoded.raw.constants), ordered);
                let decoded = quadratic_fixture(decoded, &f);
                let native_id = decoded.id;
                let native_writer = crate::core::proto::v2::CircuitWriter::new(&f);
                let native_bytes = native_writer.to_bytes(&decoded);
                let prover = ZkProver::new(decoded, config, &interpolation).unwrap();
                let mut rng = SimpleRng { state: 42 };
                let (proof, geometry) = super::prove_standalone(
                    &prover,
                    LABEL,
                    &witness_inputs[..1],
                    witness_inputs[1..].to_vec(),
                    &interpolation,
                    &mut rng,
                )
                .unwrap();
                let proof_bytes = proof.into_bytes();
                if let Some(expected) = &expected_proof {
                    assert_eq!(&proof_bytes, expected);
                } else {
                    expected_proof = Some(proof_bytes.clone());
                }
                // Proving must not change storage, segmentation, or ID.
                assert_eq!(prover.circuit.id, native_id);
                assert_eq!(native_writer.to_bytes(&prover.circuit), native_bytes);
                let verifier = ZkVerifier::new(prover.circuit, config, &interpolation).unwrap();
                let verifier_geometry = verifier.geometry();
                assert_eq!(geometry, verifier_geometry);
                let decoded_proof = super::read_standalone(
                    &verifier,
                    LABEL,
                    &witness_inputs[..1],
                    &proof_bytes,
                    &f,
                )
                .unwrap();
                let reduce = |p: &ZkProof<2, Gf2_128Field>| {
                    super::reduce_standalone(
                        &verifier,
                        LABEL,
                        &witness_inputs[..1],
                        p,
                        &interpolation,
                    )
                };
                // Both roles end in one transcript state: the prover's seal
                // checks on the authenticated session.
                let statement = verifier.statement(LABEL, &witness_inputs[..1]).unwrap();
                let mut session = Transcript::new(&statement);
                let parsed =
                    ZkProof::read(&proof_bytes, &session.bound(&statement.geometry), &f).unwrap();
                assert!(reduce(&decoded_proof).unwrap().check_seal(parsed).is_ok());

                for slot in 0..2 {
                    let mut tampered_claim = decoded_proof.clone();
                    let claims = &mut tampered_claim.sumcheck_proof.layers[0].claims;
                    f.add(&mut claims[slot], &f.one());
                    assert!(reduce(&tampered_claim).is_err());
                }
                // A malformed proof fails the owned session; it cannot return
                // a continuation that a caller could use after the error.
                let mut bad_sumcheck = decoded_proof.clone();
                bad_sumcheck.sumcheck_proof.layers[0].rounds.pop();
                let mut bad_polygero = decoded_proof.clone();
                bad_polygero.com_proof.bodies.0.h.pop();
                for malformed in [&bad_sumcheck, &bad_polygero] {
                    assert!(reduce(malformed).is_err());
                }
                let mut tampered = decoded_proof.clone();
                let value = &mut tampered.sumcheck_proof.layers[0].rounds[0].coefficients[0];
                f.add(value, &f.one());
                assert!(reduce(&tampered).is_err());
            }
        }
    }
}

#[test]
fn test_zk_triple_zero_zero_zero() {
    let f = Gf2_128Field::new();

    // One triple (0, 0, 0) with k = 0 representing assert 0 = 1 (when w[0] is 1).
    let term = Term {
        k: f.zero(),
        g: 0,
        h0: 0,
        h1: 0,
    };
    // 1 wire, 0 pubin, 1 output. logv = 0, layer_logw = 0!
    let raw = make_raw_circuit(&f, 1, 0, 1, 0, &[1], &[0], vec![vec![term]]);
    let circ = quadratic_fixture(Circuit { raw, id: [0u8; 32] }, &f);

    // To test ZK proof generation and verification cleanly on this logv=0, logw=0 circuit,
    // we set w0[0] = 0 so the constraint 0 * 0 == 0 is satisfied.
    let w0 = [false; 1];

    let make_interpolator = BinaryInterpolatorFactory::full_field(&f);
    let mut rng = SimpleRng { state: 42 };
    const LABEL: &[u8] = b"test_zk_zero";

    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    let prover_inst = ZkProver::new(circ, config, &make_interpolator).unwrap();
    let npublic = prover_inst.circuit.raw.npublic_input;
    let (encoded, _) = super::prove_standalone(
        &prover_inst,
        LABEL,
        &w0[..npublic],
        w0[npublic..].to_vec(),
        &make_interpolator,
        &mut rng,
    )
    .expect("Failed to prove ZK with logv=0, logw=0");

    let verifier = ZkVerifier::new(prover_inst.circuit, config, &make_interpolator).unwrap();
    let zkp = super::read_standalone(
        &verifier,
        LABEL,
        &w0[..verifier.public_input_count()],
        encoded.as_bytes(),
        &f,
    )
    .unwrap();
    let verify_res = super::reduce_standalone(
        &verifier,
        LABEL,
        &w0[..verifier.public_input_count()],
        &zkp,
        &make_interpolator,
    );

    assert!(
        verify_res.is_ok(),
        "ZK Verification failed for logv=0, logw=0: {:?}",
        verify_res.err()
    );
}

#[test]
fn test_zk_intermediate_zero_logw() {
    let f = Gf2_128Field::new();

    // Layer 0 (output layer): squares the single wire from layer 1: v[0] = w[0] * w[0]
    let layer0_terms = vec![Term {
        k: f.one(),
        g: 0,
        h0: 0,
        h1: 0,
    }];

    // Layer 1 (intermediate layer): squares the single wire from layer 2: v[0] = w[0] * w[0]
    // Notice this intermediate layer has 1 input wire, so logw = 0!
    let layer1_terms = vec![Term {
        k: f.one(),
        g: 0,
        h0: 0,
        h1: 0,
    }];

    // Layer 2 (input layer): takes 4 inputs (w[0]=1, w[1]=a, w[2]=b, w[3]=c),
    // and computes v[0] = 1*w[1] + 1*w[2] + 1*w[3] = a + b + c.
    // Since w[0] = 1, we can write w[i] as 1 * w[0] * w[i].
    let layer2_terms = vec![
        Term {
            k: f.one(),
            g: 0,
            h0: 0,
            h1: 1,
        },
        Term {
            k: f.one(),
            g: 0,
            h0: 0,
            h1: 2,
        },
        Term {
            k: f.one(),
            g: 0,
            h0: 0,
            h1: 3,
        },
    ];

    // ninput = 4 (logw = 2 at input layer 2), logw = 0 at layer 1, logw = 0 at layer 0. noutput = 1
    // (logv = 0).
    let raw = make_raw_circuit(
        &f,
        4,
        0,
        1,
        0,
        &[1, 1, 4],
        &[0, 0, 2],
        vec![layer0_terms, layer1_terms, layer2_terms],
    );
    let circ = quadratic_fixture(Circuit { raw, id: [0u8; 32] }, &f);

    // The three bit inputs sum to zero in characteristic two.
    let w0 = [true, true, false, true];

    // Check that plain evaluation succeeds (sum is 0, squared twice is 0)
    let eval_res = eval_circuit(
        w0.iter()
            .map(|bit| if *bit { f.one() } else { f.zero() })
            .collect(),
        &circ,
        &f,
    );
    assert!(
        eval_res.is_ok(),
        "Plain circuit evaluation failed: {:?}",
        eval_res.err()
    );

    // Now test ZK proof generation and verification
    let make_interpolator = BinaryInterpolatorFactory::full_field(&f);
    let mut rng = SimpleRng { state: 9999 };
    const LABEL: &[u8] = b"test_zk_interm";

    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    let prover_inst = ZkProver::new(circ, config, &make_interpolator).unwrap();
    let npublic = prover_inst.circuit.raw.npublic_input;
    let (encoded, _) = super::prove_standalone(
        &prover_inst,
        LABEL,
        &w0[..npublic],
        w0[npublic..].to_vec(),
        &make_interpolator,
        &mut rng,
    )
    .expect("Failed to prove ZK with intermediate logw=0");

    let verifier = ZkVerifier::new(prover_inst.circuit, config, &make_interpolator).unwrap();
    let zkp = super::read_standalone(
        &verifier,
        LABEL,
        &w0[..verifier.public_input_count()],
        encoded.as_bytes(),
        &f,
    )
    .unwrap();
    let verify_res = super::reduce_standalone(
        &verifier,
        LABEL,
        &w0[..verifier.public_input_count()],
        &zkp,
        &make_interpolator,
    );

    assert!(
        verify_res.is_ok(),
        "ZK Verification failed for intermediate logw=0: {:?}",
        verify_res.err()
    );
}

#[test]
fn test_zk_zero_layers() {
    let f = Gf2_128Field::new();

    let make_interpolator = BinaryInterpolatorFactory::full_field(&f);
    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    // Try all 16 combinations of zero / non-zero across the 4 inputs
    for mask in 0u32..16 {
        let raw = make_raw_circuit(&f, 4, 2, 4, 2, &[], &[], vec![]);
        let circ = quadratic_fixture(Circuit { raw, id: [0u8; 32] }, &f);

        let mut w0 = [false; 4];
        for (i, elem) in w0.iter_mut().enumerate().take(4) {
            if (mask & (1 << i)) != 0 {
                *elem = true; // non-zero
            }
        }

        let eval_res = eval_circuit(
            w0.iter()
                .map(|bit| if *bit { f.one() } else { f.zero() })
                .collect(),
            &circ,
            &f,
        );

        let mut rng = SimpleRng {
            state: 9999 + mask as u64,
        };
        const LABEL: &[u8] = b"test_zk_zero_layers";

        let prover_inst = ZkProver::new(circ, config, &make_interpolator).unwrap();
        let prove_res = super::prove_standalone(
            &prover_inst,
            LABEL,
            &w0[..2],
            w0[2..].to_vec(),
            &make_interpolator,
            &mut rng,
        );

        if mask == 0 {
            assert!(
                eval_res.is_ok(),
                "eval_circuit failed for all zero inputs: {:?}",
                eval_res.err()
            );
            assert!(
                prove_res.is_ok(),
                "prove failed for all zero inputs: {:?}",
                prove_res.err()
            );
            let (encoded, _) = prove_res.unwrap();

            let verifier =
                ZkVerifier::new(prover_inst.circuit, config, &make_interpolator).unwrap();
            let zkp =
                super::read_standalone(&verifier, LABEL, &w0[..2], encoded.as_bytes(), &f).unwrap();
            let verify_res =
                super::reduce_standalone(&verifier, LABEL, &w0[..2], &zkp, &make_interpolator);
            assert!(
                verify_res.is_ok(),
                "verify failed for all zero inputs: {:?}",
                verify_res.err()
            );
        } else {
            let first_nonzero = mask.trailing_zeros() as usize;
            let expected_eval_error =
                format!("Circuit output at index {first_nonzero} is not zero");
            assert_eq!(
                eval_res.unwrap_err(),
                expected_eval_error,
                "eval_circuit failed at the wrong check for input mask {mask}"
            );
            assert_eq!(
                prove_res.err().expect("invalid output must fail proving"),
                format!("eval_circuit failed: {expected_eval_error}"),
                "prove failed at the wrong check for input mask {mask}"
            );
        }
    }
}
