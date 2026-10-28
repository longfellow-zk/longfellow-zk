// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Degree-separated streams must prove the same polynomial without a One wire.
use crate::{
    core::{
        algebra::{SerializableField, SupportsU64Conversions},
        proto::{
            circuit::{compute_id, Circuit, RawCircuit},
            reader::CircuitReader,
            writer::CircuitWriter,
            FieldID, Layer, TermDelta,
        },
    },
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        random::{DeterministicRng, RandomEngine, Transcript},
        sumcheck_v2::{
            eval_circuit, prove, prover::sample_pads, verifier::verify, SumcheckProofGeometry,
        },
    },
};

fn stream<F: SerializableField>(nw: usize, terms: &[(u32, u32, u32, u32)]) -> Layer<F> {
    let mut prev = [0u32; 3];
    let deltas = terms
        .iter()
        .map(|&(g, l, r, k_index)| {
            let d = TermDelta {
                g: g.wrapping_sub(prev[0]),
                h: [l.wrapping_sub(prev[1]), r.wrapping_sub(prev[2])],
                k_index,
            };
            prev = [g, l, r];
            d
        })
        .collect();
    Layer::new_compressed(nw, crate::util::ceil_log2(nw), vec![deltas], vec![0])
}

fn check<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(f: &F) {
    // x*y + k*x + c - z = 0. No circuit input is a reserved constant.
    let mut random = DeterministicRng::new(197);
    let x = random.elt_field(f);
    let y = random.elt_field(f);
    let k = random.elt_field(f);
    let constant = random.elt_field(f);
    let mut z = f.mulf(&x, &y);
    f.fma(&mut z, &k, &x);
    f.add(&mut z, &constant);
    let inputs = vec![x, y, z];
    let q = stream::<F>(3, &[(0, 0, 1, 0)]);
    let l = stream::<F>(3, &[(0, 0, 0, 1), (0, 2, 0, 2)]);
    let c = stream::<F>(3, &[(0, 0, 0, 3)]);
    let raw = RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one(), k, f.mone(), constant],
        layers: vec![q.with_affine(l, c)],
    };
    let circuit = Circuit {
        id: compute_id(f, &raw),
        raw,
    };
    let bytes = CircuitWriter::new(f, FieldID::None).to_bytes_lfc2(&circuit);
    assert_eq!(&bytes[..4], b"LFD2");
    let (circuit, tail) = CircuitReader::new(f, FieldID::None)
        .from_bytes_lfc2(&bytes, true)
        .unwrap();
    assert!(tail.is_empty());
    assert_eq!(circuit.raw.layers[0].num_terms(), 4);
    assert!(CircuitReader::new(f, FieldID::None)
        .with_total_term_limit(3)
        .from_bytes(&bytes, true)
        .is_err());
    for i in 0..bytes.len() {
        assert!(CircuitReader::new(f, FieldID::None)
            .from_bytes(&bytes[..i], true)
            .is_err());
    }
    let mut rng = DeterministicRng::new(42);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&circuit), &mut rng, f);
    let witnesses = eval_circuit(inputs.clone(), &circuit, f).unwrap();
    let (proof, constraints) = prove(
        witnesses,
        &pads,
        &circuit,
        &mut Transcript::new(b"degrees"),
        f,
    );
    assert!(constraints
        .residuals(&inputs, &pads, f)
        .unwrap()
        .iter()
        .all(|x| f.is_zero(x)));
    verify(
        inputs.clone(),
        &pads,
        &circuit,
        &proof,
        &mut Transcript::new(b"degrees"),
        f,
    )
    .unwrap();
    let mut bad = inputs.clone();
    f.add(&mut bad[2], &f.one());
    assert!(eval_circuit(bad.clone(), &circuit, f).is_err());
    assert!(verify(
        bad,
        &pads,
        &circuit,
        &proof,
        &mut Transcript::new(b"degrees"),
        f
    )
    .is_err());
    let mut corrupted = bytes.clone();
    let last = corrupted.len() - 1;
    corrupted[last] ^= 1;
    assert!(CircuitReader::new(f, FieldID::None)
        .from_bytes(&corrupted, true)
        .is_err());
}
#[test]
fn degree_streams_prime() {
    check(&crate::runtime::algebra::p256::P256Field::new());
}
#[test]
fn degree_streams_binary() {
    check(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
}

#[cfg(feature = "degree-separated")]
#[test]
fn degree_compiler_removes_one_and_evaluates_multiple_layers() {
    use crate::{
        compile::{
            compiler::{compile_degree_separated as compile_v2, segment_circuit},
            logic::{Logic, LogicIO},
        },
        runtime::algebra::p256::P256Field,
    };
    let cf = crate::compile::algebra::p256::P256Field::new();
    let (c, geometry, _) = compile_v2(&cf, |logic| {
        let x = logic.input(1);
        let y = logic.input(2);
        let expected = logic.input(3);
        let shifted = logic.add(&logic.mul(&x, &y), &logic.one());
        let square = logic.mul(&shifted, &shifted);
        (logic.assert_eq("result", &square, &expected), 2, 0)
    });
    assert_eq!(geometry.ninput, 3);
    assert_eq!(geometry.npublic_input, 1);
    assert!(c.raw.layers.iter().all(|l| l.affine().is_some()));
    let c = segment_circuit(&cf, &c);
    let f = P256Field::new();
    let bytes = CircuitWriter::new(&cf, FieldID::P256).to_bytes_lfc2(&c);
    let (c, _) = CircuitReader::new(&f, FieldID::P256)
        .from_bytes(&bytes, true)
        .unwrap();
    let inputs = vec![
        f.u64_to_element(2),
        f.u64_to_element(3),
        f.u64_to_element(49),
    ];
    let witnesses = eval_circuit(inputs.clone(), &c, &f).unwrap();
    let mut rng = DeterministicRng::new(42);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, &f);
    let (proof, _) = prove(
        witnesses,
        &pads,
        &c,
        &mut Transcript::new(b"degree-compiler"),
        &f,
    );
    verify(
        inputs,
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"degree-compiler"),
        &f,
    )
    .unwrap();
}

#[test]
fn degree_scalar_linear_layer_has_no_rounds_or_one_input() {
    use crate::{core::algebra::AlgebraicField, runtime::algebra::p256::P256Field};
    let f = P256Field::new();
    let raw = RawCircuit {
        ninput: 1,
        npublic_input: 0,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one(), f.u64_to_element(9)],
        layers: vec![
            stream(1, &[]).with_affine(stream(1, &[(0, 0, 0, 0)]), stream(1, &[(0, 0, 0, 1)]))
        ],
    };
    let c = Circuit {
        id: compute_id(&f, &raw),
        raw,
    };
    let inputs = vec![f.neg(&f.u64_to_element(9))];
    let w = eval_circuit(inputs.clone(), &c, &f).unwrap();
    let mut rng = DeterministicRng::new(38);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, &f);
    let (proof, _) = prove(w, &pads, &c, &mut Transcript::new(b"degree-scalar"), &f);
    assert!(proof.layers[0].rounds.is_empty());
    verify(
        inputs,
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"degree-scalar"),
        &f,
    )
    .unwrap();
}

#[test]
fn degree_reader_rejects_affine_assertions_and_indices() {
    use crate::{core::algebra::AlgebraicField, runtime::algebra::p256::P256Field};
    let f = P256Field::new();
    for (g, h, k) in [(0, 3, 0), (1, 0, 0), (0, 0, 1)] {
        let raw = RawCircuit {
            ninput: 3,
            npublic_input: 0,
            noutput: 1,
            logv: 0,
            subfield_boundary: 0,
            constants: vec![f.one(), f.zero()],
            layers: vec![stream(3, &[]).with_affine(stream(3, &[(g, h, 0, k)]), stream(3, &[]))],
        };
        let c = Circuit {
            id: compute_id(&f, &raw),
            raw,
        };
        let bytes = CircuitWriter::new(&f, FieldID::P256).to_bytes_lfc2(&c);
        assert!(CircuitReader::new(&f, FieldID::P256)
            .from_bytes(&bytes, true)
            .is_err());
    }
}

#[cfg(feature = "coefficient-separated")]
fn check_coefficients<const W: usize, FC, FR>(cf: &FC, f: &FR)
where
    FC: crate::compile::algebra::field::CompileField + SerializableField + Clone,
    FR: RuntimeField<W> + SerializableField + SupportsSampling,
{
    use crate::compile::{
        compiler::{compile_degree_separated, segment_circuit},
        logic::{Logic, LogicIO},
    };
    let scalar = |n: u8| {
        let mut bytes = vec![0; cf.serialized_size_bytes()];
        bytes[0] = n;
        cf.bytes_to_element(&bytes).unwrap()
    };
    let (c, _, _) = compile_degree_separated(cf, |logic| {
        let x = logic.input(1);
        let y = logic.input(2);
        let target = logic.input(3);
        let aux = logic.input(4);
        let xy = logic.quadratic(&scalar(7), &x, &y);
        let linear = logic.mulk(&scalar(3), &x);
        let shifted = logic.add(&logic.add(&xy, &linear), &logic.konst(&scalar(5)));
        let value = logic.mul(&shifted, &shifted);
        (
            logic.assert_all(
                "checks",
                &[
                    logic.assert_eq("value", &value, &target),
                    logic.assert0("aux", &aux),
                ],
            ),
            2,
            0,
        )
    });
    assert!(c
        .raw
        .layers
        .iter()
        .flat_map(Layer::streams)
        .all(|s| s.coefficients().is_some()));
    let c = segment_circuit(cf, &c);
    let bytes = CircuitWriter::new(cf, FieldID::None).to_bytes_lfc2(&c);
    assert_eq!(
        &bytes[..4],
        if cfg!(feature = "assertion-separated") {
            b"LFD4"
        } else {
            b"LFD3"
        }
    );
    let (c, rest) = CircuitReader::new(f, FieldID::None)
        .from_bytes(&bytes, true)
        .unwrap();
    assert!(rest.is_empty());
    let scalar = |n: u8| {
        let mut b = vec![0; f.serialized_size_bytes()];
        b[0] = n;
        f.bytes_to_element(&b).unwrap()
    };
    let x = scalar(2);
    let y = scalar(11);
    let mut value = f.mulf(&scalar(7), &f.mulf(&x, &y));
    f.fma(&mut value, &scalar(3), &x);
    f.add(&mut value, &scalar(5));
    value = f.mulf(&value, &value);
    let inputs = vec![x, y, value, f.zero()];
    let w = eval_circuit(inputs.clone(), &c, f).unwrap();
    let mut rng = DeterministicRng::new(93);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, f);
    let (proof, constraints) = prove(w, &pads, &c, &mut Transcript::new(b"coefficient-arrays"), f);
    assert!(constraints
        .residuals(&inputs, &pads, f)
        .unwrap()
        .iter()
        .all(|e| f.is_zero(e)));
    verify(
        inputs.clone(),
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"coefficient-arrays"),
        f,
    )
    .unwrap();
    let mut bad = inputs.clone();
    bad[3] = f.one();
    assert!(eval_circuit(bad, &c, f).is_err());
    let mut bad = inputs;
    f.add(&mut bad[2], &f.one());
    assert!(verify(
        bad,
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"coefficient-arrays"),
        f
    )
    .is_err());
    let terms = c.raw.layers.iter().map(Layer::num_terms).sum::<usize>();
    assert!(CircuitReader::new(f, FieldID::None)
        .with_total_term_limit(terms - 1)
        .from_bytes(&bytes, true)
        .is_err());
    for n in 0..bytes.len() {
        assert!(CircuitReader::new(f, FieldID::None)
            .from_bytes(&bytes[..n], true)
            .is_err());
    }
    let mut malformed = bytes;
    let end = malformed.len() - 1;
    malformed[end] ^= 1;
    assert!(CircuitReader::new(f, FieldID::None)
        .from_bytes(&malformed, true)
        .is_err());
}
#[cfg(feature = "coefficient-separated")]
#[test]
fn coefficient_arrays_binary() {
    check_coefficients(
        &crate::compile::algebra::gf2_128::Gf2_128Field::new(),
        &crate::runtime::algebra::gf2_128::Gf2_128Field::new(),
    );
}
#[cfg(feature = "coefficient-separated")]
#[test]
fn coefficient_arrays_prime() {
    check_coefficients(
        &crate::compile::algebra::p256::P256Field::new(),
        &crate::runtime::algebra::p256::P256Field::new(),
    );
}
#[cfg(feature = "coefficient-separated")]
#[test]
fn coefficient_arrays_sextic() {
    check_coefficients(
        &crate::compile::algebra::fp24_ext6::CompileFp24Ext6::new(),
        &crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new(),
    );
}

#[cfg(feature = "coefficient-separated")]
#[test]
fn coefficient_arrays_boolean_windows_match_generic() {
    use crate::{
        compile::{
            compiler::compile_degree_separated,
            logic::{Logic, LogicIO},
        },
        runtime::{
            algebra::{gf2_128::Gf2_128Field, AlgebraicField},
            sumcheck_v2::{
                boolean::BooleanKernel, prover::prove_core_with_kernel, TranscriptSumcheck,
            },
        },
    };
    let cf = crate::compile::algebra::gf2_128::Gf2_128Field::new();
    let (c, _, _) = compile_degree_separated(&cf, |l| {
        let x = l.input(1);
        let y = l.input(2);
        let target = l.input(3);
        let aux = l.input(4);
        let value = l.mul(&l.add(&l.add(&x, &y), &l.one()), &x);
        (
            l.assert_all(
                "checks",
                &[
                    l.assert_eq("result", &value, &target),
                    l.assert0("aux", &aux),
                ],
            ),
            2,
            0,
        )
    });
    let bytes = CircuitWriter::new(&cf, FieldID::Gf2_128).to_bytes_lfc2(&c);
    let f = Gf2_128Field::new();
    let (c, _) = CircuitReader::new(&f, FieldID::Gf2_128)
        .from_bytes(&bytes, true)
        .unwrap();
    let inputs = vec![f.one(), f.zero(), f.zero(), f.zero()];
    let w = eval_circuit(inputs.clone(), &c, &f).unwrap();
    let mut rng = DeterministicRng::new(93);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, &f);
    let expected = prove(
        w.clone(),
        &pads,
        &c,
        &mut Transcript::new(b"coefficient-boolean"),
        &f,
    );
    for window in 1..=4 {
        let kernel = BooleanKernel::new(&c, window).unwrap();
        let mut t = Transcript::new(b"coefficient-boolean");
        t.write_sumcheck_statement(&c, &inputs[..c.raw.npublic_input], &f);
        let actual = prove_core_with_kernel(w.clone(), &pads, &c, &mut t, &f, &kernel);
        assert_eq!(actual, expected);
    }
}

#[cfg(feature = "assertion-separated")]
#[test]
fn assertion_kinds_remove_product_wires_and_reject_false_inputs() {
    use crate::{
        compile::{
            compiler::{compile_degree_separated, segment_circuit},
            logic::{Logic, LogicIO},
        },
        runtime::algebra::{p256::P256Field, AlgebraicField},
    };
    let cf = crate::compile::algebra::p256::P256Field::new();
    let f = P256Field::new();
    // The shallow product assertion must use its factors directly while another
    // assertion keeps the circuit deep. Its product result is never materialized.
    let (c, info, _) = compile_degree_separated(&cf, |l| {
        let a = l.input(1);
        let b = l.input(2);
        let c = l.input(3);
        let product = l.mul(&a, &b);
        let square = l.mul(&c, &c);
        let fourth = l.mul(&square, &square);
        (
            l.assert_all(
                "checks",
                &[l.assert0("product", &product), l.assert0("fourth", &fourth)],
            ),
            1,
            0,
        )
    });
    assert!(
        info.nwires <= 3,
        "product result or squared assertion was materialized"
    );
    let c = segment_circuit(&cf, &c);
    let bytes = CircuitWriter::new(&cf, FieldID::P256).to_bytes_lfc2(&c);
    let (c, _) = CircuitReader::new(&f, FieldID::P256)
        .from_bytes(&bytes, true)
        .unwrap();
    let counts = c.term_breakdown(&f);
    assert_eq!(counts[0][0], 2);
    assert_eq!(counts[1][0], 0);
    let inputs = vec![f.zero(), f.u64_to_element(7), f.zero()];
    let w = eval_circuit(inputs.clone(), &c, &f).unwrap();
    let mut rng = DeterministicRng::new(51);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, &f);
    let (proof, _) = prove(w, &pads, &c, &mut Transcript::new(b"assertion-kind"), &f);
    verify(
        inputs.clone(),
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"assertion-kind"),
        &f,
    )
    .unwrap();
    let mut bad = inputs;
    bad[0] = f.one();
    assert!(eval_circuit(bad.clone(), &c, &f).is_err());
    assert!(verify(
        bad,
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"assertion-kind"),
        &f
    )
    .is_err());
    // With two linear assertions, wire zero being zero must not make a nonzero
    // second wire look valid through an implicit multiplication by wire zero.
    let (c, _, _) = compile_degree_separated(&cf, |l| {
        let a = l.input(1);
        let b = l.input(2);
        (
            l.assert_all("zeros", &[l.assert0("a", &a), l.assert0("b", &b)]),
            1,
            0,
        )
    });
    let bytes = CircuitWriter::new(&cf, FieldID::P256).to_bytes_lfc2(&c);
    let (c, _) = CircuitReader::new(&f, FieldID::P256)
        .from_bytes(&bytes, true)
        .unwrap();
    assert_eq!(c.term_breakdown(&f)[0][0], 0);
    assert_eq!(c.term_breakdown(&f)[1][0], 2);
    let inputs = vec![f.zero(), f.zero()];
    let w = eval_circuit(inputs.clone(), &c, &f).unwrap();
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, &f);
    let (proof, _) = prove(w, &pads, &c, &mut Transcript::new(b"linear-assertions"), &f);
    verify(
        inputs,
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"linear-assertions"),
        &f,
    )
    .unwrap();
    assert!(eval_circuit(vec![f.zero(), f.one()], &c, &f).is_err());
    assert!(verify(
        vec![f.zero(), f.one()],
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"linear-assertions"),
        &f
    )
    .is_err());
}
