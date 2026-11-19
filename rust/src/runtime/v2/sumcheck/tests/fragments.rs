// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::super::fragments::*;
use crate::{
    core::{
        algebra::{RegisteredField, SerializableField},
        proto::v2::{Circuit, Constant, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{p256::P256Field, RuntimeField, SupportsSampling},
        random::{DeterministicRng, RandomEngine},
        v2::{
            proto::sumcheck::SumcheckProof,
            sumcheck::{
                classes::classify_layers, derive_constraints_for_circuits as derive,
                prove_circuits as prove, sample_pads_for_test,
            },
            transcript::Transcript,
        },
    },
};

/// Draw stage `stage`'s weights from a fresh boundary and enter the stage.
fn draw_and_enter<F: RuntimeField + RegisteredField + SupportsSampling>(
    schedule: &Schedule,
    stage: usize,
    entering: &mut Vec<F::E>,
    active: &mut [ActiveFragment<'_, F::E>],
    t: &mut Transcript,
    f: &F,
) {
    t.send_for_test(&(stage as u64).to_le_bytes());
    let drawn = t.borrow().draw(|r| schedule.draw_stage(stage, r, f));
    schedule.enter(stage, drawn, entering, active);
}

fn check_early_output_weights(short_has_layer: bool) {
    use crate::{
        core::algebra::AlgebraicField,
        runtime::{algebra::gf2_128::Gf2_128Field, v2::proto::sumcheck::LayerProof},
    };
    let f = Gf2_128Field::new();
    let make = |layers| {
        let raw = RawCircuitBuilder {
            ninput: 1,
            npublic_input: 0,
            noutput: 1,
            logv: 0,
            constants: vec![f.zero(), f.one()],
            layers,
        }
        .build();
        Circuit::from_raw(&f, raw)
    };
    let identity = || {
        Layer::new(
            1,
            Stream::<Quadratic>::from_terms([]),
            Stream::<Linear>::from_terms([Linear { g: 0, l: 0, k: 1 }]),
            Stream::<Constant>::from_terms([]),
        )
    };
    // The first circuit has identically zero output. The shorter circuit
    // asserts that their shared input is zero, which is false here. Include
    // a nonzero-depth shorter circuit: the problem is not limited to inputs.
    let mut long_layers = vec![Layer::new(
        1,
        Stream::<Quadratic>::from_terms([]),
        Stream::<Linear>::from_terms([]),
        Stream::<Constant>::from_terms([]),
    )];
    if short_has_layer {
        long_layers.push(identity());
    }
    let long = make(long_layers);
    let short = make(if short_has_layer {
        vec![identity()]
    } else {
        vec![]
    });
    let circuits = [&long, &short];
    // The earlier claim can include a guessed future coefficient, but the
    // real coefficient is drawn only after that claim is fixed.
    let guessed_output = f.one();
    // B=0 satisfies the first terminal product for every A. Its false A
    // must nevertheless fail the freshly sampled later output assertion.
    let mut proof = SumcheckProof {
        layers: vec![LayerProof {
            rounds: vec![],
            cross: f.zero(),
            claims: [f.addf(&f.one(), &guessed_output), f.zero()],
        }],
    };
    if short_has_layer {
        proof.layers.push(LayerProof {
            rounds: vec![],
            cross: f.zero(),
            claims: [f.one(), f.addf(&f.one(), &guessed_output)],
        });
    }
    let pads = SumcheckProof {
        layers: vec![
            LayerProof {
                rounds: vec![],
                cross: f.zero(),
                claims: [f.zero(), f.zero()],
            };
            proof.layers.len()
        ],
    };
    let constraints = derive(
        &circuits,
        &proof,
        &mut Transcript::for_test(b"early-output-counterexample").borrow(),
        &f,
    )
    .unwrap();
    assert!(
        constraints
            .residuals(&[f.one()], &pads, &f)
            .unwrap()
            .iter()
            .any(|x| !f.is_zero(x)),
        "false output from a shorter circuit was accepted"
    );
}

#[test]
fn early_output_weights_cannot_hide_a_false_zero_layer_output() {
    check_early_output_weights(false);
}

#[test]
fn early_output_weights_cannot_hide_a_false_shorter_circuit_output() {
    check_early_output_weights(true);
}

fn fixture<F: RuntimeField + SerializableField>(f: &F) -> [Circuit<F>; 4] {
    let layer = |nw, q, l, k| {
        Layer::new(
            nw,
            Stream::<Quadratic>::from_terms(q),
            Stream::<Linear>::from_terms(l),
            Stream::<Constant>::from_terms(k),
        )
    };
    let circuit = |layers, noutput| {
        let raw = RawCircuitBuilder {
            ninput: 4,
            npublic_input: 1,
            noutput,
            logv: crate::util::ceil_log2(noutput),
            constants: vec![f.zero(), f.one(), f.mone()],
            layers,
        }
        .build();
        Circuit::from_raw(f, raw)
    };
    let long = circuit(
        vec![
            layer(
                3,
                vec![Quadratic {
                    g: 0,
                    l: 2,
                    r: 0,
                    k: 0,
                }],
                vec![
                    Linear { g: 0, l: 0, k: 2 },
                    Linear { g: 0, l: 1, k: 1 },
                    Linear { g: 0, l: 2, k: 0 },
                ],
                vec![],
            ),
            layer(
                4,
                vec![Quadratic {
                    g: 1,
                    l: 1,
                    r: 2,
                    k: 1,
                }],
                vec![Linear { g: 0, l: 0, k: 1 }, Linear { g: 2, l: 3, k: 1 }],
                vec![],
            ),
        ],
        1,
    );
    let short = circuit(
        vec![layer(
            4,
            vec![Quadratic {
                g: 0,
                l: 1,
                r: 2,
                k: 1,
            }],
            vec![Linear { g: 0, l: 0, k: 2 }, Linear { g: 0, l: 3, k: 0 }],
            vec![],
        )],
        1,
    );
    let wide = circuit(
        vec![
            layer(
                5,
                vec![Quadratic {
                    g: 0,
                    l: 1,
                    r: 2,
                    k: 1,
                }],
                vec![
                    Linear { g: 0, l: 0, k: 2 },
                    Linear { g: 0, l: 3, k: 0 },
                    Linear { g: 0, l: 4, k: 1 },
                ],
                vec![Constant { g: 0, k: 2 }],
            ),
            layer(
                4,
                vec![],
                (0..4).map(|i| Linear { g: i, l: i, k: 1 }).collect(),
                vec![Constant { g: 4, k: 1 }],
            ),
        ],
        1,
    );
    [long, short, wide, circuit(vec![], 4)]
}
fn check<F: RuntimeField + RegisteredField + SupportsSampling>(f: &F) {
    let all = fixture(f);
    let mut rng = DeterministicRng::new(8191);
    for pattern in [
        vec![0],
        vec![1, 0, 1],
        vec![2, 0, 2, 1],
        vec![0, 2, 1, 2, 0],
        vec![3],
        vec![3, 0, 2],
    ] {
        let circuits: Vec<_> = pattern.iter().map(|&i| &all[i]).collect();
        let schedule = Schedule::new(&circuits, f).unwrap();
        let x = if pattern.contains(&3) {
            f.zero()
        } else {
            rng.elt_field(f)
        };
        let y = if pattern.contains(&3) {
            f.zero()
        } else {
            rng.elt_field(f)
        };
        let inputs = vec![f.mulf(&x, &y), x, y, f.zero()];
        let (pads, _) = sample_pads_for_test(&schedule.geometry, &mut rng, f);
        let mut tp = Transcript::for_test(b"shared-wires");
        let mut tv = Transcript::for_test(b"shared-wires");
        let (proof, c) = prove(&circuits, inputs.clone(), &pads, &mut tp.borrow(), f).unwrap();
        let d = derive(&circuits, &proof, &mut tv.borrow(), f).unwrap();
        // The top weights' boundary, then one per round and two per layer:
        // every later stage's weights extend the preceding combine answer.
        let expected_flips =
            1 + schedule.geometry.layers().iter().sum::<usize>() + 2 * schedule.layers.len();
        assert_eq!(tp.round_count_for_test(), expected_flips as u64);
        assert_eq!(tv.round_count_for_test(), expected_flips as u64);
        assert_eq!(c, d);
        assert_eq!(c.input_weights.len(), inputs.len());
        assert!(d
            .residuals(&inputs, &pads, f)
            .unwrap()
            .iter()
            .all(|x| f.is_zero(x)));
        let bytes = proof.write(&schedule.geometry, f).unwrap();
        let mut remaining = bytes.as_slice();
        let decoded = SumcheckProof::<F>::read(&mut remaining, &schedule.geometry, f).unwrap();
        assert!(remaining.is_empty());
        assert_eq!(decoded.write(&schedule.geometry, f).unwrap(), bytes);
        if !proof.layers.is_empty() {
            let mut forged = decoded;
            f.add(&mut forged.layers[0].claims[1], &f.one());
            let d = derive(
                &circuits,
                &forged,
                &mut Transcript::for_test(b"shared-wires").borrow(),
                f,
            )
            .unwrap();
            assert!(d
                .residuals(&inputs, &pads, f)
                .unwrap()
                .iter()
                .any(|v| !f.is_zero(v)));
        }
        let mut bad = inputs;
        f.add(&mut bad[0], &f.one());
        assert!(prove(
            &circuits,
            bad,
            &pads,
            &mut Transcript::for_test(b"shared-wires").borrow(),
            f
        )
        .is_err());
    }
    let schedule = Schedule::new(&[&all[0], &all[2], &all[0]], f).unwrap();
    assert_eq!(schedule.layers[0].nw, 11); // 3+5+3, with no per-circuit padding.
    assert_eq!(schedule.geometry.layers(), vec![4, 2]);
    assert_eq!(
        schedule.layers[0]
            .fragments
            .iter()
            .map(|s| s.input_range.clone())
            .collect::<Vec<_>>(),
        vec![0..3, 3..8, 8..11]
    );
    assert!(schedule.layers[1]
        .fragments
        .iter()
        .all(|s| s.input_range == (0..4)));
    assert!(Schedule::new::<F>(&[] as &[&Circuit<F>], f).is_err());
}
#[test]
fn shared_inputs_unequal_depths_widths_and_circuit_counts() {
    check(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
    check(&P256Field::new());
}

#[test]
fn depth_order_uses_the_bound_input_index_for_ties_and_duplicates() {
    let f = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    let all = fixture(&f);
    // Original positions 1, 2 and 4 have equal depth; 1 and 4 are duplicates.
    let circuits = [&all[1], &all[2], &all[0], &all[3], &all[2]];
    let schedule = Schedule::new(&circuits, &f).unwrap();
    let order = |stage: usize| {
        schedule.layers[stage]
            .fragments
            .iter()
            .map(|s| s.circuit)
            .collect::<Vec<_>>()
    };
    assert_eq!(order(0), [1, 2, 4]);
    assert_eq!(order(1), [1, 2, 4, 0]);
    assert_eq!(schedule.layers[0].output_assertions, 3);
    assert_eq!(schedule.layers[1].output_assertions, 1);
    assert_eq!(
        schedule.layers[1].nv - schedule.layers[1].output_assertions,
        schedule.layers[0].nw
    );
}

// Materialize the same concatenation independently by shifting raw gate indices.
// Compare every saved witness, both contractions and the affine correction.
fn compare_merged<F: RuntimeField + RegisteredField + SupportsSampling>(f: &F) {
    let all = fixture(f);
    let circuits = [&all[0], &all[2], &all[0]];
    let schedule = Schedule::new(&circuits, f).unwrap();
    let mut merged_layers = Vec::new();
    for stage in 0..2 {
        let mut q = Vec::new();
        let mut l = Vec::new();
        let mut k = Vec::new();
        let mut output_offset = 0;
        let mut input_offset = 0;
        for c in circuits {
            let layer = &c.raw.layers[stage];
            layer.quadratic.for_each(|mut t| {
                t.g += output_offset;
                t.l += input_offset;
                t.r += input_offset;
                q.push(t);
            });
            layer.linear.for_each(|mut t| {
                t.g += output_offset;
                t.l += input_offset;
                l.push(t);
            });
            layer.constant.for_each(|mut t| {
                t.g += output_offset;
                k.push(t);
            });
            output_offset += if stage == 0 {
                c.raw.noutput
            } else {
                c.raw.layers[0].nw
            } as u32;
            if stage == 0 {
                input_offset += layer.nw as u32;
            }
        }
        merged_layers.push(Layer::new(
            if stage == 0 { input_offset as usize } else { 4 },
            Stream::<Quadratic>::from_terms(q),
            Stream::<Linear>::from_terms(l),
            Stream::<Constant>::from_terms(k),
        ));
    }
    let raw = RawCircuitBuilder {
        ninput: 4,
        npublic_input: 1,
        noutput: 3,
        logv: 2,
        constants: all[0].raw.constants.clone(),
        layers: merged_layers,
    }
    .build();
    let merged = Circuit::from_raw(f, raw);
    let splits: Vec<_> = circuits.iter().map(|c| classify_layers(c, f)).collect();
    let merged_splits = classify_layers(&merged, f);
    let mut rng = DeterministicRng::new(913);
    let x = rng.elt_field(f);
    let y = rng.elt_field(f);
    let inputs = vec![f.mulf(&x, &y), x, y, f.zero()];
    let actual =
        super::super::eval::eval_circuits(inputs.clone(), &circuits, &splits, &schedule, f)
            .unwrap();
    let expected =
        super::super::eval::eval_classified_circuit(inputs.clone(), &merged, &merged_splits, f)
            .unwrap();
    assert_eq!(actual, expected);
    let (pads, _) = sample_pads_for_test(&schedule.geometry, &mut rng, f);
    let mut fragmented_t = Transcript::for_test(b"same-global-circuit");
    let mut merged_t = Transcript::for_test(b"same-global-circuit");
    prove(
        &circuits,
        inputs.clone(),
        &pads,
        &mut fragmented_t.borrow(),
        f,
    )
    .unwrap();
    prove(&[&merged], inputs, &pads, &mut merged_t.borrow(), f).unwrap();
    assert_eq!(
        fragmented_t.round_count_for_test(),
        merged_t.round_count_for_test()
    );
    for (stage, layout) in schedule.layers.iter().enumerate() {
        let a = rng.elt_field_slice(layout.nv, f);
        let point = rng.elt_field_slice(schedule.geometry.layers()[stage], f);
        let alpha = rng.elt_field(f);
        let mut active = Vec::new();
        let mut q = vec![f.zero(); layout.nw];
        for s in &layout.fragments {
            active.push(ActiveFragment::new(s, schedule.classify(&circuits, s)));
        }
        let mut fragmented_t = Transcript::for_test(b"same-layer-assertions");
        let mut merged_t = Transcript::for_test(b"same-layer-assertions");
        let mut entering = Vec::new();
        if stage > 0 {
            entering.resize(layout.nv, f.zero());
        }
        draw_and_enter(
            &schedule,
            stage,
            &mut entering,
            &mut active,
            &mut fragmented_t,
            f,
        );
        let merged_list = [&merged];
        let merged_schedule = Schedule::new(&merged_list, f).unwrap();
        let merged_fragment = &merged_schedule.layers[stage].fragments[0];
        let mut merged_active = vec![ActiveFragment::new(
            merged_fragment,
            merged_schedule.classify(&merged_list, merged_fragment),
        )];
        let mut merged_entering = Vec::new();
        if stage > 0 {
            merged_entering.resize(layout.nv, f.zero());
        }
        draw_and_enter(
            &merged_schedule,
            stage,
            &mut merged_entering,
            &mut merged_active,
            &mut merged_t,
            f,
        );
        assert_eq!(entering, merged_entering);
        let merged_assertions = &merged_active[0].assertions;
        let mut flattened = Vec::new();
        for kind in 0..2 {
            for a in &active {
                let nq = a.layer.assertion_counts()[0];
                flattened.extend_from_slice(if kind == 0 {
                    &a.assertions[..nq]
                } else {
                    &a.assertions[nq..]
                });
            }
        }
        assert_eq!(&flattened, merged_assertions);
        assert_eq!(fragmented_t.round_count_for_test(), 1);
        assert_eq!(merged_t.round_count_for_test(), 1);
        assert_eq!(fragmented_t.bytes(32), merged_t.bytes(32));
        for fragment in &active {
            let s = &fragment.fragment;
            super::super::quad::bind_r_into(
                &fragment.layer,
                &circuits[s.circuit].raw.constants,
                &a[s.output_range.clone()],
                &fragment.assertions,
                &actual[stage][s.input_range.clone()],
                &mut q[s.input_range.clone()],
                f,
            );
        }
        let reference = super::super::quad::bind_r(
            &merged_splits[stage],
            &merged.raw.constants,
            &a,
            merged_assertions,
            &actual[stage],
            f,
        );
        assert_eq!(q, reference);
        let transition = super::super::fragments::transition(
            &circuits, &a, &active, layout.nw, &point, &alpha, f,
        );
        let expected = super::super::quad::weights_next_affine(
            &merged_splits[stage],
            &merged.raw.constants,
            &a,
            merged_assertions,
            &point,
            &alpha,
            f,
        );
        assert_eq!(transition, expected);
    }
}
#[test]
fn quad_fragments_match_a_physically_merged_circuit() {
    compare_merged(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
    compare_merged(&P256Field::new());
}

/// Components may declare different input widths. Each reads a prefix of the
/// shared input array, whose width is the largest declared width.
fn check_prefix_widths<F: RuntimeField + RegisteredField + SupportsSampling>(f: &F) {
    let layer = |nw: usize, quadratic: Vec<Quadratic>, linear: Vec<Linear>| {
        Layer::new(
            nw,
            Stream::<Quadratic>::from_terms(quadratic),
            Stream::<Linear>::from_terms(linear),
            Stream::default(),
        )
    };
    let circuit_with = |ninput: usize, npublic_input: usize, l: Layer| {
        let raw = RawCircuitBuilder {
            ninput,
            npublic_input,
            noutput: 1,
            logv: 0,
            constants: vec![f.one(), f.mone()],
            layers: vec![l],
        }
        .build();
        Circuit::from_raw(f, raw)
    };
    let circuit = |ninput: usize, l: Layer| circuit_with(ninput, 0, l);
    let wide_layer = |nw: usize| {
        layer(
            nw,
            vec![],
            vec![Linear { g: 0, l: 4, k: 0 }, Linear { g: 0, l: 0, k: 1 }],
        )
    };
    // Narrow: x*y - in[0] over inputs 0..3. Wide: in[4] - in[0] over 0..5.
    let narrow = circuit(
        3,
        layer(
            3,
            vec![Quadratic {
                g: 0,
                l: 1,
                r: 2,
                k: 0,
            }],
            vec![Linear { g: 0, l: 0, k: 1 }],
        ),
    );
    let wide = circuit(5, wide_layer(5));
    let schedule = Schedule::new(&[&narrow, &wide], f).unwrap();
    assert_eq!(schedule.ninput, 5);
    assert_eq!(
        schedule.layers[0]
            .fragments
            .iter()
            .map(|s| s.input_range.clone())
            .collect::<Vec<_>>(),
        vec![0..3, 0..5]
    );
    let mut rng = DeterministicRng::new(77);
    let (x, y) = (rng.elt_field(f), rng.elt_field(f));
    let xy = f.mulf(&x, &y);
    let inputs = vec![xy.clone(), x, y, rng.elt_field(f), xy];
    let (pads, _) = sample_pads_for_test(&schedule.geometry, &mut rng, f);
    let circuits = [&narrow, &wide];
    let (proof, c) = prove(
        &circuits,
        inputs.clone(),
        &pads,
        &mut Transcript::for_test(b"prefix-widths").borrow(),
        f,
    )
    .unwrap();
    let d = derive(
        &circuits,
        &proof,
        &mut Transcript::for_test(b"prefix-widths").borrow(),
        f,
    )
    .unwrap();
    assert_eq!(c, d);
    assert_eq!(d.input_weights.len(), 5);
    assert!(d
        .residuals(&inputs, &pads, f)
        .unwrap()
        .iter()
        .all(|v| f.is_zero(v)));
    // Only the wide component reads input 4.
    let mut bad = inputs;
    f.add(&mut bad[4], &f.one());
    assert!(prove(
        &circuits,
        bad,
        &pads,
        &mut Transcript::for_test(b"prefix-widths").borrow(),
        f
    )
    .is_err());
    // The public prefix must match, and each component's input layer must
    // span exactly its own declared width.
    let public = circuit_with(5, 1, wide_layer(5));
    assert!(Schedule::new(&[&narrow, &public], f).is_err());
    let short = circuit(5, wide_layer(4));
    assert!(Schedule::new(&[&narrow, &short], f).is_err());
}
#[test]
fn components_read_prefixes_of_one_shared_input_array() {
    check_prefix_widths(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
    check_prefix_widths(&P256Field::new());
}
