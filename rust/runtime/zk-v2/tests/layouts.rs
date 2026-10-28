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
    core::proto::{
        circuit::{compare_term, Circuit, Layer, RawCircuit, Term, TermDelta},
        reader::CircuitReader,
        SerializableField,
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
            subfield_v1::BinarySubfield, AlgebraicField, RuntimeField,
        },
        polygero::PolygeroConfig,
        random::{RandomEngine, Transcript},
        zk_v2::{ZkProof, ZkProver, ZkVerifier},
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

        let unrolled_deltas: Vec<crate::core::proto::TermDelta> = delta_segment
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
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);

    // 1. Manually build a simple 1-layer circuit
    let term = Term {
        k: f.one(),
        g: 0,
        h0: 0,
        h1: 1,
    };
    let raw = make_raw_circuit(&f, 2, 0, 1, 0, &[2], &[1], vec![vec![term]]);
    let circ = Circuit { raw, id: [0u8; 32] };

    // 2. Setup inputs
    let mut w0 = [f.zero(); 2];
    w0[0] = f.one();
    w0[1] = f.zero();

    // 3. Prover commit
    let make_interpolator = BinaryInterpolatorFactory::new(&f, &subfield);

    let mut rng = SimpleRng { state: 42 };
    let mut ts_prover = Transcript::new(b"test_zk");

    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    let prover_inst = ZkProver::new_full_field(circ, config);
    let (prover, geom) = prover_inst
        .commit(
            w0[prover_inst.circuit.raw.npublic_input..].to_vec(),
            &crate::runtime::zk_v2::ZkContext {
                f: &f,
                domain: &make_interpolator,
            },
            &mut ts_prover,
            &mut rng,
        )
        .unwrap();

    // 4. Prover prove
    let zkp = prover_inst
        .prove(
            &w0[..prover_inst.circuit.raw.npublic_input],
            prover,
            &mut ts_prover,
            &crate::runtime::zk_v2::ZkContext {
                f: &f,
                domain: &make_interpolator,
            },
        )
        .expect("Failed to prove");
    // 5. Serialize / deserialize proof roundtrip
    let serialized = zkp.write(&geom, &f).expect("Failed to serialize ZkProof");
    let mut verifier = ZkVerifier::new_full_field(
        prover_inst.circuit,
        config,
        &crate::runtime::zk_v2::ZkContext {
            f: &f,
            domain: &make_interpolator,
        },
    )
    .unwrap();
    let v_geom = verifier.geometry();
    let mut r_slice = serialized.as_slice();
    let deserialized =
        ZkProof::read(&mut r_slice, &v_geom, &f).expect("Failed to deserialize ZkProof");
    assert!(r_slice.is_empty());
    assert_eq!(
        zkp, deserialized,
        "Deserialized proof is not equal to original proof!"
    );

    // 6. Verifier verify
    let mut ts_verifier = Transcript::new(b"test_zk");
    verifier.receive_commitment(&deserialized, &mut ts_verifier);

    let verify_res = verifier.verify(
        &w0[..verifier.public_input_count()],
        &deserialized,
        &mut ts_verifier,
        &crate::runtime::zk_v2::ZkContext {
            f: &f,
            domain: &make_interpolator,
        },
    );

    assert!(verify_res.is_ok(), "ZK Verification failed: {verify_res:?}");
}

#[test]
fn test_zk_supported_layouts_multibit_roundtrip_and_tampering() {
    use crate::core::{
        algebra::SupportsU128Conversions,
        proto::{circuit::compute_id, writer::CircuitWriter, FieldID},
    };

    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let interpolation = BinaryInterpolatorFactory::new(&f, &sf);
    let context = crate::runtime::zk_v2::ZkContext {
        f: &f,
        domain: &interpolation,
    };
    // A non-power-of-two width exercises several sumcheck rounds and input pairs
    // (0,3)/(2,2), whose Morton and lexicographic orders differ.
    let inputs: Vec<_> = (1..=7).map(|v| f.u128_to_element(v)).collect();
    let mut terms = Vec::new();
    let mut sum = f.zero();
    for h0 in 0..7 {
        for h1 in h0..7 {
            f.fma(&mut sum, &inputs[h0], &inputs[h1]);
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

        // All-zero witnesses exercise a zero final claim.
        let zero_inputs = vec![f.zero(); inputs.len()];
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
                let prover = ZkProver::new_full_field(decoded, config);
                let mut rng = SimpleRng { state: 42 };
                let mut prover_ts = Transcript::new(b"lexicographic-zk");
                let (commitment, geometry) = prover
                    .commit(
                        witness_inputs[1..].to_vec(),
                        &context,
                        &mut prover_ts,
                        &mut rng,
                    )
                    .unwrap();
                let proof = prover
                    .prove(&witness_inputs[..1], commitment, &mut prover_ts, &context)
                    .unwrap();
                let proof_bytes = proof.write(&geometry, &f).unwrap();
                if let Some(expected) = &expected_proof {
                    assert_eq!(&proof_bytes, expected);
                } else {
                    expected_proof = Some(proof_bytes.clone());
                }
                // Proving must not change storage, segmentation, or ID.
                assert_eq!(prover.circuit.id, circuit.id);
                assert_eq!(
                    prover.circuit.raw.layers[0].terms(&prover.circuit.raw.constants),
                    ordered
                );
                let mut verifier =
                    ZkVerifier::new_full_field(prover.circuit, config, &context).unwrap();
                let verifier_geometry = verifier.geometry();
                assert_eq!(geometry, verifier_geometry);
                let mut remaining = proof_bytes.as_slice();
                let decoded_proof = ZkProof::read(&mut remaining, &verifier_geometry, &f).unwrap();
                assert!(remaining.is_empty());
                assert_eq!(proof, decoded_proof);
                let mut verifier_ts = Transcript::new(b"lexicographic-zk");
                verifier.receive_commitment(&decoded_proof, &mut verifier_ts);
                verifier
                    .verify(
                        &witness_inputs[..1],
                        &decoded_proof,
                        &mut verifier_ts,
                        &context,
                    )
                    .unwrap();
                assert_eq!(prover_ts.bytes(64), verifier_ts.bytes(64));

                for slot in 0..2 {
                    let mut tampered_claim = decoded_proof.clone();
                    let claims = &mut tampered_claim.sumcheck_proof.layers[0].claims;
                    f.add(&mut claims[slot], &f.one());
                    let mut bad_ts = Transcript::new(b"lexicographic-zk");
                    verifier.receive_commitment(&tampered_claim, &mut bad_ts);
                    assert!(verifier
                        .verify(&witness_inputs[..1], &tampered_claim, &mut bad_ts, &context)
                        .is_err());
                }
                // Reject either protocol's malformed messages before consuming
                // any sumcheck challenges, even after receiving the root.
                let mut bad_sumcheck = decoded_proof.clone();
                bad_sumcheck.sumcheck_proof.layers[0].rounds.pop();
                let mut bad_polygero = decoded_proof.clone();
                bad_polygero.com_proof.h.pop();
                for malformed in [&bad_sumcheck, &bad_polygero] {
                    let mut bad_ts = Transcript::new(b"lexicographic-zk");
                    verifier.receive_commitment(malformed, &mut bad_ts);
                    let mut unchanged = bad_ts.clone();
                    assert!(verifier
                        .verify(&witness_inputs[..1], malformed, &mut bad_ts, &context)
                        .is_err());
                    assert_eq!(bad_ts.bytes(64), unchanged.bytes(64));
                }
                let mut tampered = decoded_proof;
                let value = &mut tampered.sumcheck_proof.layers[0].rounds[0].coefficients[0];
                f.add(value, &f.one());
                let mut bad_ts = Transcript::new(b"lexicographic-zk");
                verifier.receive_commitment(&tampered, &mut bad_ts);
                assert!(verifier
                    .verify(&witness_inputs[..1], &tampered, &mut bad_ts, &context)
                    .is_err());
            }
        }
    }
}

#[test]
fn test_zk_triple_zero_zero_zero() {
    let f = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);

    // One triple (0, 0, 0) with k = 0 representing assert 0 = 1 (when w[0] is 1).
    let term = Term {
        k: f.zero(),
        g: 0,
        h0: 0,
        h1: 0,
    };
    // 1 wire, 0 pubin, 1 output. logv = 0, layer_logw = 0!
    let raw = make_raw_circuit(&f, 1, 0, 1, 0, &[1], &[0], vec![vec![term]]);
    let circ = Circuit { raw, id: [0u8; 32] };

    // To test ZK proof generation and verification cleanly on this logv=0, logw=0 circuit,
    // we set w0[0] = 0 so the constraint 0 * 0 == 0 is satisfied.
    let w0 = [f.zero(); 1];

    let make_interpolator = BinaryInterpolatorFactory::new(&f, &subfield);
    let mut rng = SimpleRng { state: 42 };
    let mut ts_prover = Transcript::new(b"test_zk_zero");

    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    let prover_inst = ZkProver::new_full_field(circ, config);
    let (commit_res, _geom) = prover_inst
        .commit(
            w0[prover_inst.circuit.raw.npublic_input..].to_vec(),
            &crate::runtime::zk_v2::ZkContext {
                f: &f,
                domain: &make_interpolator,
            },
            &mut ts_prover,
            &mut rng,
        )
        .unwrap();

    let zkp = prover_inst
        .prove(
            &w0[..prover_inst.circuit.raw.npublic_input],
            commit_res,
            &mut ts_prover,
            &crate::runtime::zk_v2::ZkContext {
                f: &f,
                domain: &make_interpolator,
            },
        )
        .expect("Failed to prove ZK with logv=0, logw=0");

    let mut verifier = ZkVerifier::new_full_field(
        prover_inst.circuit,
        config,
        &crate::runtime::zk_v2::ZkContext {
            f: &f,
            domain: &make_interpolator,
        },
    )
    .unwrap();
    let mut ts_verifier = Transcript::new(b"test_zk_zero");
    verifier.receive_commitment(&zkp, &mut ts_verifier);

    let verify_res = verifier.verify(
        &w0[..verifier.public_input_count()],
        &zkp,
        &mut ts_verifier,
        &crate::runtime::zk_v2::ZkContext {
            f: &f,
            domain: &make_interpolator,
        },
    );

    assert!(
        verify_res.is_ok(),
        "ZK Verification failed for logv=0, logw=0: {:?}",
        verify_res.err()
    );
}

#[test]
fn test_zk_intermediate_zero_logw() {
    use crate::core::algebra::SupportsU128Conversions;
    let f = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);

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
    let circ = Circuit { raw, id: [0u8; 32] };

    // Let's set inputs such that a + b + c = 0 in GF(2^128).
    // In characteristic 2, addition is XOR. Let a = 10, b = 20 => c = 10 ^ 20 = 30.
    let mut w0 = vec![f.zero(); 4];
    w0[0] = f.one();
    w0[1] = f.u128_to_element(10);
    w0[2] = f.u128_to_element(20);
    w0[3] = f.u128_to_element(30);

    // Check that plain evaluation succeeds (sum is 0, squared twice is 0)
    let eval_res = crate::runtime::sumcheck_v2::eval_circuit(w0.clone(), &circ, &f);
    assert!(
        eval_res.is_ok(),
        "Plain circuit evaluation failed: {:?}",
        eval_res.err()
    );

    // Now test ZK proof generation and verification
    let make_interpolator = BinaryInterpolatorFactory::new(&f, &subfield);
    let mut rng = SimpleRng { state: 9999 };
    let mut ts_prover = Transcript::new(b"test_zk_interm");

    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    let prover_inst = ZkProver::new_full_field(circ, config);
    let (commit_res, _geom) = prover_inst
        .commit(
            w0[prover_inst.circuit.raw.npublic_input..].to_vec(),
            &crate::runtime::zk_v2::ZkContext {
                f: &f,
                domain: &make_interpolator,
            },
            &mut ts_prover,
            &mut rng,
        )
        .unwrap();

    let zkp = prover_inst
        .prove(
            &w0[..prover_inst.circuit.raw.npublic_input],
            commit_res,
            &mut ts_prover,
            &crate::runtime::zk_v2::ZkContext {
                f: &f,
                domain: &make_interpolator,
            },
        )
        .expect("Failed to prove ZK with intermediate logw=0");

    let mut verifier = ZkVerifier::new_full_field(
        prover_inst.circuit,
        config,
        &crate::runtime::zk_v2::ZkContext {
            f: &f,
            domain: &make_interpolator,
        },
    )
    .unwrap();
    let mut ts_verifier = Transcript::new(b"test_zk_interm");
    verifier.receive_commitment(&zkp, &mut ts_verifier);

    let verify_res = verifier.verify(
        &w0[..verifier.public_input_count()],
        &zkp,
        &mut ts_verifier,
        &crate::runtime::zk_v2::ZkContext {
            f: &f,
            domain: &make_interpolator,
        },
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
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);

    let make_interpolator = BinaryInterpolatorFactory::new(&f, &subfield);
    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 4,
    };

    // Try all 16 combinations of zero / non-zero across the 4 inputs
    for mask in 0u32..16 {
        let raw = make_raw_circuit(&f, 4, 2, 4, 2, &[], &[], vec![]);
        let circ = Circuit { raw, id: [0u8; 32] };

        let mut w0 = vec![f.zero(); 4];
        for (i, elem) in w0.iter_mut().enumerate().take(4) {
            if (mask & (1 << i)) != 0 {
                *elem = f.one(); // non-zero
            }
        }

        let eval_res = crate::runtime::sumcheck_v2::eval_circuit(w0.clone(), &circ, &f);

        let mut rng = SimpleRng {
            state: 9999 + mask as u64,
        };
        let mut ts_prover = Transcript::new(b"test_zk_zero_layers");

        let prover_inst = ZkProver::new_full_field(circ, config);
        let (commit_res, _geom) = prover_inst
            .commit(
                w0[2..].to_vec(),
                &crate::runtime::zk_v2::ZkContext {
                    f: &f,
                    domain: &make_interpolator,
                },
                &mut ts_prover,
                &mut rng,
            )
            .unwrap();

        let prove_res = prover_inst.prove(
            &w0[..2],
            commit_res,
            &mut ts_prover,
            &crate::runtime::zk_v2::ZkContext {
                f: &f,
                domain: &make_interpolator,
            },
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
            let zkp = prove_res.unwrap();

            let mut verifier = ZkVerifier::new_full_field(
                prover_inst.circuit,
                config,
                &crate::runtime::zk_v2::ZkContext {
                    f: &f,
                    domain: &make_interpolator,
                },
            )
            .unwrap();
            let mut ts_verifier = Transcript::new(b"test_zk_zero_layers");
            verifier.receive_commitment(&zkp, &mut ts_verifier);

            let verify_res = verifier.verify(
                &w0[..2],
                &zkp,
                &mut ts_verifier,
                &crate::runtime::zk_v2::ZkContext {
                    f: &f,
                    domain: &make_interpolator,
                },
            );
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
                prove_res.unwrap_err(),
                format!("eval_circuit failed: {expected_eval_error}"),
                "prove failed at the wrong check for input mask {mask}"
            );
        }
    }
}
