// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Exercise all eleven concrete classes together, including independent assertions.
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{
            Circuit, Constant, ConstantCoordinates, Layer, Linear, LinearCoordinates, Quadratic,
            QuadraticCoordinates, RawCircuit, Stream,
        },
    },
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        random::{DeterministicRng, Transcript},
        sumcheck_v2::{
            eval::eval_layer,
            eval_circuit, prove,
            prover::sample_pads,
            quad::{bind_l, bind_r, weights_next_affine},
            verifier::verify,
            SumcheckProofGeometry,
        },
    },
};
fn all_classes<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling + Clone,
>(
    f: &F,
) {
    let scalar = |n: u8| {
        let mut bytes = vec![0; f.serialized_size_bytes()];
        bytes[0] = n;
        f.bytes_to_element(&bytes).unwrap()
    };
    let (x, y) = (scalar(2), scalar(7));
    let (kq, kl) = (scalar(3), scalar(5));
    let mut value = f.mulf(&kq, &f.mulf(&x, &y));
    f.fma(&mut value, &y, &y);
    f.fma(&mut value, &kl, &y);
    f.add(&mut value, &x);
    f.add(&mut value, &f.one());
    f.fnms(&mut value, &x, &x);
    f.sub(&mut value, &y);
    f.sub(&mut value, &f.one());
    let constants = vec![kq, kl, f.neg(&value)];
    let layer =
        Layer {
            nw: 3,
            logw: 2,
            quadratic: Stream::<Quadratic>::from_terms([Quadratic {
                g: 0,
                l: 0,
                r: 1,
                k: 0,
            }]),
            quadratic_one: Stream::<QuadraticCoordinates>::from_terms([QuadraticCoordinates {
                g: 0,
                l: 1,
                r: 1,
            }]),
            quadratic_assertions: Stream::<QuadraticCoordinates>::from_terms([
                QuadraticCoordinates { g: 1, l: 0, r: 2 },
            ]),
            linear: Stream::<Linear>::from_terms([Linear { g: 0, l: 1, k: 1 }]),
            linear_one: Stream::<LinearCoordinates>::from_terms([LinearCoordinates { g: 0, l: 0 }]),
            linear_assertions: Stream::<LinearCoordinates>::from_terms([LinearCoordinates {
                g: 1,
                l: 2,
            }]),
            constant: Stream::<Constant>::from_terms([Constant { g: 0, k: 2 }]),
            constant_one: Stream::<ConstantCoordinates>::from_terms([ConstantCoordinates { g: 0 }]),
            quadratic_minus_one: Stream::<QuadraticCoordinates>::from_terms([
                QuadraticCoordinates { g: 0, l: 0, r: 0 },
            ]),
            linear_minus_one: Stream::<LinearCoordinates>::from_terms([LinearCoordinates {
                g: 0,
                l: 1,
            }]),
            constant_minus_one: Stream::<ConstantCoordinates>::from_terms([ConstantCoordinates {
                g: 0,
            }]),
        };
    assert_eq!(
        layer.term_class_breakdown(),
        [[1, 1, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1]]
    );
    // Check the binding on an arbitrary, unsatisfied witness and rho values so
    // assertion terms cannot disappear merely because a valid witness is zero.
    let w = [x.clone(), y.clone(), scalar(11)];
    let a = [scalar(13), f.zero()];
    let rho = [scalar(17), scalar(19)];
    let ql = bind_r(&layer, &constants, &a, &rho, &w, f);
    let expected0 = f.addf(
        &f.addf(&f.mulf(&f.mulf(&a[0], &constants[0]), &w[1]), &a[0]),
        &f.mulf(&rho[0], &w[2]),
    );
    let expected1 = f.addf(&f.mulf(&a[0], &w[1]), &f.mulf(&a[0], &constants[1]));
    let expected0 = f.subf(&expected0, &f.mulf(&a[0], &w[0]));
    let expected1 = f.subf(&expected1, &a[0]);
    assert_eq!(ql, [expected0, expected1, rho[1].clone()]);
    let point = [scalar(23), scalar(29)];
    let alpha = scalar(31);
    let m = crate::runtime::sumcheck_v2::monomial::weights(2, 3, &point, f);
    let qr = bind_l(&layer, &constants, &a, &rho, &m, f);
    let constant = crate::runtime::sumcheck_v2::quad::affine_constant(&layer, &constants, &a, f);
    let (next, linear) = weights_next_affine(&layer, &constants, &a, &rho, &point, &alpha, f);
    assert_eq!(
        blas::dot(&m, &ql, f),
        f.addf(&blas::dot(&qr, &w, f), &linear)
    );
    assert_eq!(
        blas::dot(&next, &w, f),
        f.addf(
            &blas::dot(&m, &w, f),
            &f.mulf(&alpha, &blas::dot(&qr, &w, f))
        )
    );
    assert_eq!(constant, f.mulf(&a[0], &constants[2]));
    let inputs = vec![x, y, f.zero()];
    assert!(eval_layer(&inputs, &layer, &constants, 2, f)
        .unwrap()
        .iter()
        .all(|x| f.is_zero(x)));
    let mut bad = inputs.clone();
    bad[2] = f.one();
    assert!(eval_layer(&bad, &layer, &constants, 2, f)
        .unwrap_err()
        .contains("quadratic assertion"));
    let mut linear_only = layer.clone();
    linear_only.quadratic_assertions = Stream::default();
    assert!(eval_layer(&bad, &linear_only, &constants, 2, f)
        .unwrap_err()
        .contains("linear assertion"));
    let mut c = Circuit {
        id: [71; 32],
        coefficient_classes: Default::default(),
        raw: RawCircuit {
            ninput: 3,
            npublic_input: 1,
            noutput: 2,
            logv: 1,
            subfield_boundary: 0,
            constants,
            layers: vec![layer],
        },
    };
    let mut rng = DeterministicRng::new(1234);
    let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, f);
    let witnesses = eval_circuit(inputs.clone(), &c, f).unwrap();
    let (proof, constraints) = prove(
        witnesses,
        &pads,
        &c,
        &mut Transcript::new(b"explicit-classes"),
        f,
    );
    assert!(constraints
        .residuals(&inputs, &pads, f)
        .unwrap()
        .iter()
        .all(|x| f.is_zero(x)));
    verify(
        inputs,
        &pads,
        &c,
        &proof,
        &mut Transcript::new(b"explicit-classes"),
        f,
    )
    .unwrap();
    if !f.is_binary() {
        use crate::{
            compile::compiler::segment_circuit_v2,
            core::proto::{
                archive::{CircuitArchive, CircuitArchiveBuilder},
                reader::CircuitReader,
                v2::compute_id,
                writer::CircuitWriter,
                FieldID,
            },
        };
        c.id = compute_id(f, &c.raw, c.coefficient_classes);
        let compressed = segment_circuit_v2(f, &c);
        assert_eq!(c.id, compressed.id);
        let writer = CircuitWriter::new(f, FieldID::None);
        let bytes = writer.to_bytes_lfc3(&compressed);
        let reader = CircuitReader::new(f, FieldID::None);
        let mut fragmented = std::io::BufReader::with_capacity(1, bytes.as_slice());
        let decoded = reader.from_stream_lfc3(&mut fragmented, true).unwrap();
        assert_eq!(
            decoded.term_class_breakdown(f),
            [[1, 1, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1]]
        );
        assert_eq!(writer.to_bytes_lfc3(&decoded), bytes);
        let mut builder = CircuitArchiveBuilder::new();
        builder.add_entry("all-classes", c.id, bytes.clone());
        let archive_bytes = builder.build().to_bytes();
        assert_eq!(&archive_bytes[..4], b"LFA2");
        let archive = CircuitArchive::from_bytes(&archive_bytes).unwrap();
        assert_eq!(archive.entries[0].payload, bytes);
        let decoded = reader
            .from_bytes_v2(&archive.entries[0].payload, true)
            .unwrap()
            .0;
        assert_eq!(decoded.id, archive.entries[0].circuit_id);
    }
}
#[test]
fn eleven_classes_prime() {
    all_classes(&crate::runtime::algebra::p256::P256Field::new());
}
#[test]
fn eleven_classes_binary() {
    all_classes(&crate::runtime::algebra::gf2_128::Gf2_128Field::new());
}
#[cfg(feature = "experimental")]
#[test]
fn eleven_classes_extension() {
    all_classes(&crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new());
}
#[test]
fn records_have_their_exact_arities_and_runs_retain_deltas() {
    use std::mem::size_of;
    assert_eq!(size_of::<Quadratic>(), 16);
    assert_eq!(size_of::<QuadraticCoordinates>(), 12);
    assert_eq!(size_of::<Linear>(), 12);
    assert_eq!(size_of::<LinearCoordinates>(), 8);
    assert_eq!(size_of::<Constant>(), 8);
    assert_eq!(size_of::<ConstantCoordinates>(), 4);
    let stream = Stream {
        deltas: vec![
            Linear { g: 0, l: 1, k: 3 },
            Linear {
                g: 1,
                l: u32::MAX,
                k: 7,
            },
        ],
        segments: vec![vec![0, 1]],
        tokens: vec![0, 0],
    };
    let mut actual = Vec::new();
    stream.for_each(|t| actual.push(t));
    assert_eq!(
        actual,
        vec![
            Linear { g: 0, l: 1, k: 3 },
            Linear { g: 1, l: 0, k: 7 },
            Linear { g: 1, l: 1, k: 3 },
            Linear { g: 2, l: 0, k: 7 }
        ]
    );
    let rebuilt = Stream::<Linear>::from_terms(actual.clone());
    let mut roundtrip = Vec::new();
    rebuilt.for_each(|t| roundtrip.push(t));
    assert_eq!(actual, roundtrip);
}
#[test]
fn v2_reader_rejects_quadratic_only_archives() {
    use crate::core::{
        algebra::AlgebraicField,
        proto::{
            circuit::{compute_id, Circuit, RawCircuit},
            reader::CircuitReader,
            writer::CircuitWriter,
            FieldID, Layer, TermDelta,
        },
    };
    let f = crate::runtime::algebra::p256::P256Field::new();
    let raw = RawCircuit {
        ninput: 1,
        npublic_input: 0,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one()],
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
    };
    let c = Circuit {
        id: compute_id(&f, &raw),
        raw,
    };
    let bytes = CircuitWriter::new(&f, FieldID::P256).to_bytes_lfc2(&c);
    let mut fragmented = std::io::BufReader::with_capacity(1, bytes.as_slice());
    CircuitReader::new(&f, FieldID::P256)
        .from_stream(&mut fragmented, true)
        .unwrap();
    let error = match CircuitReader::new(&f, FieldID::P256).from_bytes_v2(&bytes, true) {
        Ok(_) => panic!("accepted legacy layer"),
        Err(e) => e,
    };
    assert!(error.contains("LFC3"));
}

#[test]
fn default_v2_compiler_emits_all_classes_without_a_one_input() {
    use crate::{
        compile::{
            compiler::compile_v2,
            logic::{Logic, LogicIO},
        },
        core::{
            algebra::AlgebraicField,
            proto::{reader::CircuitReader, writer::CircuitWriter, FieldID},
        },
    };
    let cf = crate::compile::algebra::p256::P256Field::new();
    let (c, geometry, _) = compile_v2(&cf, |logic| {
        let x = logic.input(1);
        let target = logic.input(2);
        (
            logic.assert_eq("shifted", &logic.add(&x, &logic.one()), &target),
            2,
            0,
        )
    });
    assert_eq!(geometry.ninput, 2);
    assert_eq!(geometry.npublic_input, 1);
    let bytes = CircuitWriter::new(&cf, FieldID::P256).to_bytes_lfc3(&c);
    assert_eq!(&bytes[..4], b"LFC3");
    let f = crate::runtime::algebra::p256::P256Field::new();
    let (c, tail) = CircuitReader::new(&f, FieldID::P256)
        .from_bytes_v2(&bytes, true)
        .unwrap();
    assert!(tail.is_empty());
    // Zero in input slot zero must not suppress the linear equality.
    eval_circuit(vec![f.zero(), f.one()], &c, &f).unwrap();
    assert!(eval_circuit(vec![f.zero(), f.zero()], &c, &f).is_err());
}

#[test]
fn lfc3_rejects_minus_one_in_general_stream_even_without_id_enforcement() {
    use crate::{
        compile::{
            compiler::compile_v2,
            logic::{Logic, LogicIO},
        },
        core::{
            algebra::{AlgebraicField, SupportsU64Conversions},
            proto::{reader::CircuitReader, writer::CircuitWriter, FieldID},
        },
    };
    let cf = crate::compile::algebra::p256::P256Field::new();
    let (mut c, _, _) = compile_v2(&cf, |logic| {
        let x = logic.input(1);
        let y = logic.input(2);
        let target = logic.input(3);
        let value = logic.quadratic(&cf.u64_to_element(7), &x, &y);
        (logic.assert_eq("value", &value, &target), 2, 0)
    });
    let bytes = CircuitWriter::new(&cf, FieldID::P256).to_bytes_lfc3(&c);
    assert_eq!(&bytes[..4], b"LFC3");
    let f = crate::runtime::algebra::p256::P256Field::new();
    CircuitReader::new(&f, FieldID::P256)
        .from_bytes_v2(&bytes, true)
        .unwrap();
    let index = c
        .raw
        .constants
        .iter()
        .position(|k| *k == cf.u64_to_element(7))
        .unwrap();
    c.raw.constants[index] = cf.mone();
    c.id = crate::core::proto::v2::compute_id(&cf, &c.raw, c.coefficient_classes);
    let corrupt = CircuitWriter::new(&cf, FieldID::P256).to_bytes_lfc3(&c);
    assert!(CircuitReader::new(&f, FieldID::P256)
        .from_bytes_v2(&corrupt, false)
        .is_err());
}

fn policy_matrix<const W: usize, CF, RF>(cf: &CF, f: &RF)
where
    CF: crate::compile::algebra::field::CompileField + SerializableField,
    RF: RuntimeField<W> + SerializableField + SupportsSampling,
{
    use crate::{
        compile::{
            compiler::{compile_v2_with_classes, CoefficientClasses as C},
            logic::{Logic, LogicIO},
        },
        core::proto::{reader::CircuitReader, writer::CircuitWriter, FieldID},
    };
    let literal = |n: u8| {
        let mut b = vec![0; cf.serialized_size_bytes()];
        b[0] = n;
        cf.bytes_to_element(&b).unwrap()
    };
    let scalar = |n: u8| {
        let mut b = vec![0; f.serialized_size_bytes()];
        b[0] = n;
        f.bytes_to_element(&b).unwrap()
    };
    let mut geometry = None;
    for classes in [C::ASSERTIONS, C::ONE, C::MINUS_ONE, C::ALL] {
        let (c, g, _) = compile_v2_with_classes(
            cf,
            |l| {
                let x = l.input(1);
                let y = l.input(2);
                let target = l.input(3);
                let a = l.sub(&l.mul(&x, &x), &l.mul(&y, &y));
                let a = l.add(&l.sub(&a, &l.one()), &l.mulk(&literal(7), &y));
                (l.assert_eq("result", &l.add(&a, &x), &target), 2, 0)
            },
            classes,
        );
        let shape = (g.ninput, g.nwires, g.nterms, g.nlayers);
        if let Some(expected) = geometry {
            assert_eq!(expected, shape);
        } else {
            geometry = Some(shape);
        }
        let bytes = CircuitWriter::new(cf, FieldID::None).to_bytes_lfc3(&c);
        assert_eq!(&bytes[..4], b"LFC3");
        assert_eq!(bytes[4] as usize, classes.for_field(cf.is_binary()).bits());
        let (c, tail) = CircuitReader::new(f, FieldID::None)
            .from_bytes_v2(&bytes, true)
            .unwrap();
        assert!(tail.is_empty());
        for n in 0..bytes.len() {
            assert!(CircuitReader::new(f, FieldID::None)
                .from_bytes_v2(&bytes[..n], true)
                .is_err());
        }
        let (x, y) = (scalar(0), scalar(3));
        let mut target = f.subf(&f.mulf(&x, &x), &f.mulf(&y, &y));
        f.sub(&mut target, &f.one());
        f.fma(&mut target, &scalar(7), &y);
        f.add(&mut target, &x);
        let inputs = vec![x, y, target];
        let witnesses = eval_circuit(inputs.clone(), &c, f).unwrap();
        let mut rng = DeterministicRng::new(334);
        let (pads, _) = sample_pads(&SumcheckProofGeometry::from_circuit(&c), &mut rng, f);
        let (proof, _) = prove(
            witnesses,
            &pads,
            &c,
            &mut Transcript::new(b"coefficient-policy"),
            f,
        );
        verify(
            inputs.clone(),
            &pads,
            &c,
            &proof,
            &mut Transcript::new(b"coefficient-policy"),
            f,
        )
        .unwrap();
        let mut bad = inputs;
        f.add(&mut bad[2], &f.one());
        assert!(eval_circuit(bad.clone(), &c, f).is_err());
        assert!(verify(
            bad,
            &pads,
            &c,
            &proof,
            &mut Transcript::new(b"coefficient-policy"),
            f
        )
        .is_err());
        if !classes.one {
            let mut bad = bytes;
            bad[4] = 4;
            assert!(CircuitReader::new(f, FieldID::None)
                .from_bytes_v2(&bad, false)
                .is_err());
        }
    }
}
#[test]
fn coefficient_policy_matrix_prime() {
    policy_matrix(
        &crate::compile::algebra::p256::P256Field::new(),
        &crate::runtime::algebra::p256::P256Field::new(),
    );
}
#[test]
fn coefficient_policy_matrix_binary() {
    policy_matrix(
        &crate::compile::algebra::gf2_128::Gf2_128Field::new(),
        &crate::runtime::algebra::gf2_128::Gf2_128Field::new(),
    );
}
#[cfg(feature = "experimental")]
#[test]
fn coefficient_policy_matrix_extension() {
    policy_matrix(
        &crate::compile::algebra::fp24_ext6::CompileFp24Ext6::new(),
        &crate::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new(),
    );
}
