// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::proto::v2::{self, Constant, Layer, Linear, Quadratic, RawCircuit, Stream},
    runtime::{
        random::DeterministicRng,
        sumcheck_v2::{
            derive_constraints_for_circuits as derive, evaluate_and_prove_circuits as prove,
            sample_pads, split::split_layers, SumcheckProof,
        },
    },
};
fn fixture<const W: usize, F: RuntimeField<W> + SerializableField>(f: &F) -> [Circuit<F>; 4] {
    let layer = |nw, q, l, k| {
        Layer::with_assertions(
            nw,
            Stream::<Quadratic>::from_terms(q),
            Stream::<Linear>::from_terms(l),
            Stream::<Constant>::from_terms(k),
            |k| k == 0,
        )
    };
    let circuit = |layers, noutput| {
        let raw = RawCircuit {
            ninput: 4,
            npublic_input: 1,
            noutput,
            logv: crate::util::ceil_log2(noutput),
            constants: vec![f.zero(), f.one(), f.mone()],
            layers,
        };
        Circuit {
            id: v2::compute_id(f, &raw),
            raw,
        }
    };
    let long = circuit(
        vec![
            layer(
                3,
                vec![],
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
fn check<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(f: &F) {
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
        let schedule = Schedule::new(&circuits).unwrap();
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
        let (pads, _) = sample_pads(&schedule.geometry, &mut rng, f);
        let (proof, c) = prove(
            &circuits,
            inputs.clone(),
            &pads,
            &mut Transcript::new(b"shared-wires"),
            f,
        )
        .unwrap();
        let d = derive(&circuits, &proof, &mut Transcript::new(b"shared-wires"), f).unwrap();
        assert_eq!(c, d);
        assert_eq!(c.input_weights.len(), inputs.len());
        assert!(d
            .residuals(&inputs, &pads, f)
            .unwrap()
            .iter()
            .all(|x| f.is_zero(x)));
        let bytes = proof.write(&schedule.geometry, f).unwrap();
        let mut remaining = bytes.as_slice();
        let decoded = SumcheckProof::<W, F>::read(&mut remaining, &schedule.geometry, f).unwrap();
        assert!(remaining.is_empty());
        assert_eq!(decoded.write(&schedule.geometry, f).unwrap(), bytes);
        if !proof.layers.is_empty() {
            let mut forged = decoded;
            f.add(&mut forged.layers[0].claims[1], &f.one());
            let d = derive(&circuits, &forged, &mut Transcript::new(b"shared-wires"), f).unwrap();
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
            &mut Transcript::new(b"shared-wires"),
            f
        )
        .is_err());
    }
    let schedule = Schedule::new(&[&all[0], &all[2], &all[0]]).unwrap();
    assert_eq!(schedule.layers[0].nw, 11); // 3+5+3, with no per-circuit padding.
    assert_eq!(schedule.geometry.logw_layers, vec![4, 2]);
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
    assert!(Schedule::new::<F>(&[]).is_err());
}
#[test]
fn shared_inputs_unequal_depths_widths_and_circuit_counts() {
    check(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
    check(&crate::runtime::algebra::p256::P256Field::new());
}

// Materialize the same concatenation independently by shifting raw gate indices.
// Compare every saved witness, both contractions and the affine correction.
fn compare_merged<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    f: &F,
) {
    let all = fixture(f);
    let circuits = [&all[0], &all[2], &all[0]];
    let schedule = Schedule::new(&circuits).unwrap();
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
        merged_layers.push(Layer::with_assertions(
            if stage == 0 { input_offset as usize } else { 4 },
            Stream::<Quadratic>::from_terms(q),
            Stream::<Linear>::from_terms(l),
            Stream::<Constant>::from_terms(k),
            |k| k == 0,
        ));
    }
    let raw = RawCircuit {
        ninput: 4,
        npublic_input: 1,
        noutput: 3,
        logv: 2,
        constants: all[0].raw.constants.clone(),
        layers: merged_layers,
    };
    let merged = Circuit {
        id: v2::compute_id(f, &raw),
        raw,
    };
    let splits: Vec<_> = circuits.iter().map(|c| split_layers(c, f)).collect();
    let merged_splits = split_layers(&merged, f);
    let mut rng = DeterministicRng::new(913);
    let x = rng.elt_field(f);
    let y = rng.elt_field(f);
    let inputs = vec![f.mulf(&x, &y), x, y, f.zero()];
    let actual =
        super::super::eval::eval_circuits(inputs.clone(), &circuits, &splits, &schedule, f)
            .unwrap();
    let expected =
        super::super::eval::eval_split_circuit(inputs, &merged, &merged_splits, f).unwrap();
    assert_eq!(actual, expected);
    for (stage, layout) in schedule.layers.iter().enumerate() {
        let a = rng.elt_field_slice(layout.nv, f);
        let point = rng.elt_field_slice(schedule.geometry.logw_layers[stage], f);
        let alpha = rng.elt_field(f);
        // These fixtures have linear assertions only, so concatenating their
        // challenges preserves the raw merged layer's assertion traversal.
        let mut merged_assertions = Vec::new();
        let mut active = Vec::new();
        let mut q = vec![f.zero(); layout.nw];
        for s in &layout.fragments {
            let split = SplitLayer::with_classes(
                &circuits[s.circuit].raw.layers[s.layer],
                &crate::core::proto::v2::classify_constants(f, &circuits[s.circuit].raw.constants),
            );
            let assertions = rng.elt_field_slice(split.assertion_counts().iter().sum(), f);
            merged_assertions.extend_from_slice(&assertions);
            super::super::quad::bind_r_into(
                &split,
                &circuits[s.circuit].raw.constants,
                &a[s.output_range.clone()],
                &assertions,
                &actual[stage][s.input_range.clone()],
                &mut q[s.input_range.clone()],
                f,
            );
            active.push(SplitFragment {
                fragment: s.clone(),
                layer: split,
                assertions,
            });
        }
        let reference = super::super::quad::bind_r(
            &merged_splits[stage],
            &merged.raw.constants,
            &a,
            &merged_assertions,
            &actual[stage],
            f,
        );
        assert_eq!(q, reference);
        let transition = super::transition(&circuits, &a, &active, layout.nw, &point, &alpha, f);
        let expected = super::super::quad::weights_next_affine(
            &merged_splits[stage],
            &merged.raw.constants,
            &a,
            &merged_assertions,
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
    compare_merged(&crate::runtime::algebra::p256::P256Field::new());
}
