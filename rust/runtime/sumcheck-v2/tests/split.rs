// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn private_split_preserves_shared_segment_tokens_and_deltas() {
    let source = Layer::new(
        8,
        Stream {
            deltas: vec![
                Quadratic {
                    g: 1,
                    l: 1,
                    r: 1,
                    k: 0,
                },
                Quadratic {
                    g: 0,
                    l: 1,
                    r: 1,
                    k: 1,
                },
                Quadratic {
                    g: 1,
                    l: 0,
                    r: 1,
                    k: 2,
                },
                Quadratic {
                    g: 0,
                    l: 1,
                    r: 0,
                    k: 7,
                },
                Quadratic {
                    g: u32::MAX,
                    l: u32::MAX,
                    r: u32::MAX,
                    k: 1,
                },
            ],
            segments: vec![vec![0, 1, 2, 3], vec![], vec![4]],
            tokens: vec![0, 1, 2, 0],
        },
        Stream {
            deltas: vec![
                Linear { g: 0, l: 1, k: 3 },
                Linear { g: 1, l: 1, k: 0 },
                Linear { g: 0, l: 1, k: 1 },
                Linear {
                    g: u32::MAX,
                    l: u32::MAX,
                    k: 2,
                },
            ],
            segments: vec![vec![0, 1, 2], vec![3], vec![]],
            tokens: vec![0, 2, 1, 0],
        },
        Stream {
            deltas: vec![
                Constant { g: 1, k: 1 },
                Constant { g: 1, k: 2 },
                Constant { g: u32::MAX, k: 4 },
            ],
            segments: vec![vec![0, 1], vec![2], vec![]],
            tokens: vec![0, 2, 1, 0],
        },
    );
    let split = SplitLayer::new(&source);
    assert!(std::ptr::eq(
        split.quadratic_runs.tokens,
        source.quadratic.tokens.as_slice()
    ));
    assert!(std::ptr::eq(
        split.linear_runs.tokens,
        source.linear.tokens.as_slice()
    ));
    assert!(std::ptr::eq(
        split.constant_runs.tokens,
        source.constant.tokens.as_slice()
    ));
    let mut q: [Vec<Quadratic>; 4] = std::array::from_fn(|_| Vec::new());
    source.quadratic.for_each(|t| {
        q[match t.k {
            0 => 3,
            1 => 1,
            2 => 2,
            _ => 0,
        }]
        .push(t)
    });
    let mut actual = Vec::new();
    split
        .quadratic
        .for_each(&split.quadratic_runs, |t| actual.push(t));
    assert_eq!(actual, q[0]);
    for (stream, k, i) in [
        (&split.quadratic_one, 1, 1),
        (&split.quadratic_minus_one, 2, 2),
        (&split.quadratic_assertions, 0, 3),
    ] {
        let mut actual = Vec::new();
        stream.for_each(&split.quadratic_runs, |QuadraticCoordinates { g, l, r }| {
            actual.push(Quadratic { g, l, r, k })
        });
        assert_eq!(actual, q[i]);
    }
    let mut l: [Vec<Linear>; 4] = std::array::from_fn(|_| Vec::new());
    source.linear.for_each(|t| {
        l[match t.k {
            0 => 3,
            1 => 1,
            2 => 2,
            _ => 0,
        }]
        .push(t)
    });
    let mut actual = Vec::new();
    split
        .linear
        .for_each(&split.linear_runs, |t| actual.push(t));
    assert_eq!(actual, l[0]);
    for (stream, k, i) in [
        (&split.linear_one, 1, 1),
        (&split.linear_minus_one, 2, 2),
        (&split.linear_assertions, 0, 3),
    ] {
        let mut actual = Vec::new();
        stream.for_each(&split.linear_runs, |LinearCoordinates { g, l }| {
            actual.push(Linear { g, l, k })
        });
        assert_eq!(actual, l[i]);
    }
    let mut c: [Vec<Constant>; 3] = std::array::from_fn(|_| Vec::new());
    source.constant.for_each(|t| {
        c[match t.k {
            1 => 1,
            2 => 2,
            _ => 0,
        }]
        .push(t)
    });
    let mut actual = Vec::new();
    split
        .constant
        .for_each(&split.constant_runs, |t| actual.push(t));
    assert_eq!(actual, c[0]);
    for (stream, k, i) in [
        (&split.constant_one, 1, 1),
        (&split.constant_minus_one, 2, 2),
    ] {
        let mut actual = Vec::new();
        stream.for_each(&split.constant_runs, |ConstantCoordinates { g }| {
            actual.push(Constant { g, k })
        });
        assert_eq!(actual, c[i]);
    }
    assert_eq!(split.assertion_counts(), source.assertion_counts());
    assert_eq!(
        split.quadratic_assertions.num_terms(&split.quadratic_runs),
        q[3].len()
    );
    assert_eq!(
        split.linear_assertions.num_terms(&split.linear_runs),
        l[3].len()
    );
}

fn check_bindings<const W: usize, F>(f: &F)
where F: crate::runtime::algebra::RuntimeField<W>
        + crate::core::algebra::SerializableField
        + crate::runtime::algebra::SupportsSampling {
    use crate::runtime::{
        random::{DeterministicRng, RandomEngine},
        sumcheck_v2::quad,
    };
    let mut rng = DeterministicRng::new(318);
    let scalar = |n: u8| {
        let mut bytes = vec![0; f.serialized_size_bytes()];
        bytes[0] = n;
        f.bytes_to_element(&bytes).unwrap()
    };
    let constants = vec![f.zero(), f.one(), f.mone(), scalar(3), scalar(7)];
    for _ in 0..16 {
        let k = |x: u32| if x == 2 && f.is_binary() { 1 } else { x };
        let mut q = Vec::new();
        let mut l = Vec::new();
        let mut c = Vec::new();
        for i in 0..32 {
            q.push(Quadratic {
                g: (rng.u128() % 5) as u32,
                l: (rng.u128() % 7) as u32,
                r: (rng.u128() % 7) as u32,
                k: k(i % 5),
            });
            l.push(Linear {
                g: (rng.u128() % 5) as u32,
                l: (rng.u128() % 7) as u32,
                k: k(i % 5),
            });
            c.push(Constant {
                g: (rng.u128() % 5) as u32,
                k: k(i % 4 + 1),
            });
        }
        // Zero net displacement allows repeated tokens while exercising carries
        // across internal source segments, including empty split segments.
        q.push(Quadratic {
            g: 0,
            l: 0,
            r: 0,
            k: 1,
        });
        l.push(Linear { g: 0, l: 0, k: 1 });
        c.push(Constant { g: 0, k: 1 });
        fn segmented<T>(mut s: Stream<T>) -> Stream<T> {
            let run = s.segments.pop().unwrap();
            s.segments = vec![
                run[..9].to_vec(),
                vec![],
                run[9..21].to_vec(),
                run[21..].to_vec(),
            ];
            s.tokens = vec![0, 1, 2, 3, 0, 1, 2, 3];
            s
        }
        let raw = Layer::new(
            7,
            segmented(Stream::<Quadratic>::from_terms(q)),
            segmented(Stream::<Linear>::from_terms(l)),
            segmented(Stream::<Constant>::from_terms(c)),
        );
        let before = format!("{raw:?}");
        let split = SplitLayer::new(&raw);
        let mut a = (0..5).map(|_| rng.elt_field(f)).collect::<Vec<_>>();
        a[0] = f.zero();
        let rho = (0..raw.assertion_counts().iter().sum::<usize>())
            .map(|_| rng.elt_field(f))
            .collect::<Vec<_>>();
        let w = (0..7).map(|_| rng.elt_field(f)).collect::<Vec<_>>();
        let b = (0..7).map(|_| rng.elt_field(f)).collect::<Vec<_>>();
        let mut ordinary_quadratic = raw.quadratic.clone();
        for term in &mut ordinary_quadratic.deltas {
            if term.k == 0 {
                term.k = 1;
            }
        }
        let mut ordinary_linear = raw.linear.clone();
        for term in &mut ordinary_linear.deltas {
            if term.k == 0 {
                term.k = 1;
            }
        }
        let ordinary = Layer::new(
            raw.nw,
            ordinary_quadratic,
            ordinary_linear,
            raw.constant.clone(),
        );
        let ordinary_split = SplitLayer::new(&ordinary);
        assert_eq!(
            crate::runtime::sumcheck_v2::eval::eval_layer(&w, &ordinary_split, &constants, 5, f),
            super::reference::eval_layer(&w, &ordinary, &constants, 5, f)
        );
        assert_eq!(
            quad::bind_r(&split, &constants, &a, &rho, &w, f),
            super::reference::bind_r(&raw, &constants, &a, &rho, &w, f)
        );
        assert_eq!(
            quad::bind_l(&split, &constants, &a, &rho, &b, f),
            super::reference::bind_l(&raw, &constants, &a, &rho, &b, f)
        );
        assert_eq!(
            quad::affine_constant(&split, &constants, &a, f),
            super::reference::affine_constant(&raw, &constants, &a, f)
        );
        let point = (0..3).map(|_| rng.elt_field(f)).collect::<Vec<_>>();
        let alpha = rng.elt_field(f);
        assert_eq!(
            quad::weights_next_affine(&split, &constants, &a, &rho, &point, &alpha, f),
            super::reference::weights_next_affine(&raw, &constants, &a, &rho, &point, &alpha, f)
        );
        assert_eq!(
            format!("{raw:?}"),
            before,
            "split/binding mutated the original layer"
        );
    }
}
#[test]
fn split_bindings_match_three_stream_prime() {
    check_bindings(&crate::runtime::algebra::p256::P256Field::new());
}
#[test]
fn split_bindings_match_three_stream_binary() {
    check_bindings(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
}
#[cfg(feature = "experimental")]
#[test]
fn split_bindings_match_three_stream_sextic() {
    check_bindings(&crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new());
}

fn check_proof<const W: usize, F>(f: &F)
where F: crate::runtime::algebra::RuntimeField<W>
        + crate::core::algebra::SerializableField
        + crate::runtime::algebra::SupportsSampling {
    use crate::{
        core::proto::{
            v2::{compute_id, Circuit, RawCircuit},
            writer::CircuitWriter,
            FieldID,
        },
        runtime::{
            random::{DeterministicRng, RandomEngine, Transcript},
            sumcheck_v2::{self, prover::sample_pads, SumcheckProofGeometry, TranscriptSumcheck},
        },
    };
    let scalar = |n: u8| {
        let mut bytes = vec![0; f.serialized_size_bytes()];
        bytes[0] = n;
        f.bytes_to_element(&bytes).unwrap()
    };
    let x = scalar(2);
    let y = scalar(7);
    let kq = scalar(3);
    let kl = scalar(5);
    let minus = if f.is_binary() { 1 } else { 2 };
    let mut value = f.mulf(&kq, &f.mulf(&x, &y));
    f.fma(&mut value, &y, &y);
    f.fnms(&mut value, &x, &x);
    f.fma(&mut value, &kl, &y);
    f.add(&mut value, &x);
    f.sub(&mut value, &y);
    let raw = RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 2,
        logv: 1,
        subfield_boundary: 0,
        constants: vec![f.zero(), f.one(), f.mone(), kq, kl, f.neg(&value)],
        layers: vec![Layer::new(
            3,
            Stream::<Quadratic>::from_terms([
                Quadratic {
                    g: 0,
                    l: 0,
                    r: 1,
                    k: 3,
                },
                Quadratic {
                    g: 1,
                    l: 0,
                    r: 2,
                    k: 0,
                },
                Quadratic {
                    g: 0,
                    l: 1,
                    r: 1,
                    k: 1,
                },
                Quadratic {
                    g: 0,
                    l: 0,
                    r: 0,
                    k: minus,
                },
            ]),
            Stream::<Linear>::from_terms([
                Linear { g: 0, l: 1, k: 4 },
                Linear { g: 1, l: 2, k: 0 },
                Linear { g: 0, l: 0, k: 1 },
                Linear {
                    g: 0,
                    l: 1,
                    k: minus,
                },
            ]),
            Stream::<Constant>::from_terms([
                Constant { g: 0, k: 5 },
                Constant { g: 0, k: 1 },
                Constant { g: 0, k: minus },
            ]),
        )],
    };
    let circuit = Circuit {
        id: compute_id(f, &raw),
        raw,
    };
    let writer = CircuitWriter::new(f, FieldID::None);
    let bytes_before = writer.to_bytes_v2(&circuit);
    let id_before = circuit.id;
    let inputs = vec![x, y, f.zero()];
    let witnesses = super::reference::eval_circuit(inputs.clone(), &circuit, f).unwrap();
    assert_eq!(
        sumcheck_v2::eval_circuit(inputs.clone(), &circuit, f).unwrap(),
        witnesses
    );
    let mut rng = DeterministicRng::new(44);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&circuit), &mut rng, f);
    let mut actual = Transcript::new(b"private-layer-split");
    actual.write_sumcheck_statement(&circuit, &inputs[..1], f);
    let got =
        sumcheck_v2::evaluate_and_prove(inputs.clone(), &pads, &circuit, &mut actual, f).unwrap();
    let mut expected = Transcript::new(b"private-layer-split");
    expected.write_sumcheck_statement(&circuit, &inputs[..1], f);
    let reference = super::reference::prove_core(witnesses, &pads, &circuit, &mut expected, f);
    let geometry = SumcheckProofGeometry::from_circuit(&circuit);
    assert_eq!(
        got.0.write(&geometry, f).unwrap(),
        reference.0.write(&geometry, f).unwrap()
    );
    assert_eq!(got.1, reference.1);
    assert_eq!(actual.bytes(64), expected.bytes(64));
    assert_eq!(circuit.id, id_before);
    assert_eq!(writer.to_bytes_v2(&circuit), bytes_before);
    sumcheck_v2::verifier::verify(
        inputs,
        &pads,
        &circuit,
        &got.0,
        &mut Transcript::new(b"private-layer-split"),
        f,
    )
    .unwrap();
    assert_eq!(
        writer.to_bytes_v2(&circuit),
        bytes_before,
        "proving or reduction mutated the original circuit"
    );
}
#[test]
fn split_preserves_proof_transcript_and_circuit_prime() {
    check_proof(&crate::runtime::algebra::p256::P256Field::new());
}
#[test]
fn split_preserves_proof_transcript_and_circuit_binary() {
    check_proof(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
}
#[cfg(feature = "experimental")]
#[test]
fn split_preserves_proof_transcript_and_circuit_sextic() {
    check_proof(&crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new());
}
