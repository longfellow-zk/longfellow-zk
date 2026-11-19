// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Freeze v1 bytes independently while checking the native v2 circuit semantics.
use sha2::{Digest, Sha256};

use crate::{
    compile::{
        algebra::CompileField,
        compiler::{
            compile_v1, compile_v2, segment_circuit_v1, segment_circuit_v2, CompilerAssertions,
            CompilerLogic,
        },
        debug::evaluate::eval_circuit_fc,
        logic::{Logic, LogicIO},
    },
    core::{
        algebra::{FieldID, SerializableField, SupportsU64Conversions},
        proto::v1::{CircuitReader, CircuitWriter},
    },
    runtime::algebra::RuntimeField,
};
// Exercise constants, linear terms, squares, products, and multiple layers.
fn build<F: CompileField>(
    logic: CompilerLogic<'_, F>,
) -> (CompilerAssertions<'_, F>, usize, usize) {
    let x: Vec<_> = (1..=8).map(|i| logic.input(i)).collect();
    let assertions = logic.assert_mapi("outputs", 0..8, |i| {
        let product = logic.mul(&x[i], &x[(i + 1) % 8]);
        let sum = logic.add(&product, &logic.mul(&x[(i + 2) % 8], &x[(i + 2) % 8]));
        let shifted = logic.add(&sum, &logic.one());
        let value = logic.mul(&shifted, &x[(i + 3) % 8]);
        logic.assert_eq("value", &logic.input(9 + i), &value)
    });
    (assertions, 4, 6)
}

fn check<FC, FR>(fc: &FC, fr: &FR, fid: FieldID, expected: [&str; 3])
where
    FC: CompileField + Clone + SupportsU64Conversions,
    FR: RuntimeField + SerializableField,
{
    let (v1, g1, _) = compile_v1(fc, build);
    let (v2, g2, _) = compile_v2(fc, |logic| {
        let (a, n, _) = build(logic);
        (a, n)
    });
    assert_eq!(g1.ninput, g2.ninput + 1);
    assert_eq!(g1.npublic_input, g2.npublic_input + 1);
    let writer = CircuitWriter::new(fc, fid);
    let legacy = segment_circuit_v1(fc, &v1);
    let encodings = [
        writer.to_bytes_lfc1(&v1),
        writer.to_bytes_lfc2(&v1),
        writer.to_bytes_lfc2(&legacy),
    ];
    for (bytes, expected) in encodings.iter().zip(expected) {
        assert!(crate::core::proto::v2::CircuitReader::new(fr)
            .from_bytes(bytes)
            .is_err());
        assert_eq!(
            format!("{:x}", Sha256::digest(bytes)),
            expected,
            "v1 serialization changed"
        );
        let (decoded, tail) = CircuitReader::new(fr, fid).from_bytes(bytes, true).unwrap();
        assert!(tail.is_empty());
        assert_eq!(decoded.id, v1.id);
    }
    let modern = segment_circuit_v2(fc, v2);
    let encoded = crate::core::proto::v2::CircuitWriter::new(fc).to_bytes(&modern);
    assert!(CircuitReader::new(fr, fid)
        .from_bytes(&encoded, true)
        .is_err());
    let (modern, tail) = crate::core::proto::v2::CircuitReader::new(fr)
        .from_bytes(&encoded)
        .unwrap();
    let (legacy, _) = CircuitReader::new(fr, fid)
        .from_bytes(&encodings[2], true)
        .unwrap();
    assert!(tail.is_empty());
    for seed in 0..8 {
        let x: Vec<_> = (0..8)
            .map(|i| {
                fr.bytes_to_element(&fc.to_bytes(&fc.u64_to_element(seed * 8 + i)))
                    .unwrap()
            })
            .collect();
        let mut inputs = x.clone();
        for i in 0..8 {
            let p = fr.mulf(&x[i], &x[(i + 1) % 8]);
            let s = fr.addf(&p, &fr.mulf(&x[(i + 2) % 8], &x[(i + 2) % 8]));
            inputs.push(fr.mulf(&fr.addf(&s, &fr.one()), &x[(i + 3) % 8]));
        }
        crate::runtime::v2::sumcheck::eval_circuit(inputs.clone(), &modern, fr).unwrap();
        let mut old = vec![fr.one()];
        old.extend(inputs.clone());
        crate::runtime::v1::sumcheck::eval::eval_circuit(old.clone(), &legacy, fr).unwrap();
        for i in 8..16 {
            let mut bad = inputs.clone();
            fr.add(&mut bad[i], &fr.one());
            assert!(crate::runtime::v2::sumcheck::eval_circuit(bad, &modern, fr).is_err());
            let mut bad = old.clone();
            fr.add(&mut bad[i + 1], &fr.one());
            assert!(crate::runtime::v1::sumcheck::eval::eval_circuit(bad, &legacy, fr).is_err());
        }
    }
}
#[test]
fn v1_bytes_and_v2_semantics_prime() {
    check(
        &crate::compile::algebra::p256::P256Field::new(),
        &crate::runtime::algebra::p256::P256Field::new(),
        FieldID::P256,
        [
            "f4ea9af4e338315e1905302f79658fddd12a8cf1c0cbe1847b5bad5855aa4597",
            "b05d1813f794756abdef48bfc642e616dfe9407dfbd6bd5e219f51bbb7a93c01",
            "cb7d7b58eadf021d8da1ff9acffebbbedec47e67dc9eb5bc78731a5cf20e44d4",
        ],
    );
}
#[test]
fn v1_bytes_and_v2_semantics_binary() {
    check(
        &crate::compile::algebra::gf2_128::Gf2_128Field::new(),
        &crate::runtime::algebra::gf2_128::Gf2_128Field::new(),
        FieldID::Gf2_128,
        [
            "632e800486e2b1c99f592c6bc8b648118d761a2e73e02b21f80b359f2eb2719b",
            "0d268db7d5e29a813f7c9fae1daa16779ace1a85bfd6defce239b4e3e74837b2",
            "d24bc2c0918cd14a259792c34679b8039dc0652059b6ee2021fd1cff278f3610",
        ],
    );
}

#[test]
fn unused_binary_inputs_are_rejected_before_and_after_a_used_input() {
    let f = crate::compile::algebra::gf2_128::Gf2_128Field::new();
    for used in [1, 2] {
        let failure = std::panic::catch_unwind(|| {
            compile_v2(&f, |logic| {
                let inputs = [logic.input(1), logic.input(2)];
                (logic.assert0("used", &inputs[used - 1]), 1)
            });
        });
        let error = failure.expect_err("unused input accepted");
        let message = error
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| error.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(message.contains("some inputs are unused"), "{message}");
    }
}

#[test]
fn binary_input_bit_assertions_are_v1_only() {
    use crate::circuits::boolean::{Boolean, BooleanIO};
    let f = crate::compile::algebra::gf2_128::Gf2_128Field::new();
    let (_, v1, _) = compile_v1(&f, |logic| {
        let boolean = Boolean::new(&logic);
        let input = BooleanIO::new(&logic).input(1);
        (logic.assert0("zero", &boolean.as_eltw(&input)), 1, 0)
    });
    let (v2_circuit, v2, _) = compile_v2(&f, |logic| {
        let boolean = Boolean::new(&logic);
        let input = BooleanIO::new(&logic).input(1);
        (logic.assert0("zero", &boolean.as_eltw(&input)), 1)
    });
    assert_eq!(v1.nassertions, 2);
    assert_eq!(v2.nassertions, 1);
    assert!(v2_circuit
        .layers
        .iter()
        .all(|layer| layer.quadratic.num_terms() == 0));

    // An explicit field-to-bit conversion still emits its constraint in v2.
    let (checked_circuit, checked, _) = compile_v2(&f, |logic| {
        let boolean = Boolean::new(&logic);
        let input = boolean.of_eltw(logic.input(1));
        (logic.assert0("zero", &boolean.as_eltw(&input)), 1)
    });
    assert_eq!(checked.nassertions, 2);
    assert!(checked_circuit
        .layers
        .iter()
        .any(|layer| layer.quadratic.num_terms() != 0));
}

#[test]
fn v2_direct_lowering_emits_deep_constants_without_copy_chains() {
    let fc = crate::compile::algebra::p256::P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let c7 = fc.u64_to_element(7);
    let c3 = fc.u64_to_element(3);

    // ((x1 * x2) * x3) + 7 - 3 * x4 == 0
    // Layers in v2 RawCircuit are ordered output-first (layer 0 is deepest).
    // Only the deepest sum layer should carry a constant term; input->mid layers
    // must have zero constant stream terms.
    let (raw, geom, _) = compile_v2(&fc, |logic| {
        let x1 = logic.input(1);
        let x2 = logic.input(2);
        let x3 = logic.input(3);
        let x4 = logic.input(4);
        let p12 = logic.mul(&x1, &x2);
        let p123 = logic.mul(&p12, &x3);
        let plus_c = logic.add(&p123, &logic.konst(&c7));
        let rhs = logic.mulk(&c3, &x4);
        (logic.assert_eq("deep_const", &plus_c, &rhs), 2)
    });

    assert_eq!(geom.nlayers, 2);
    // Output-most layer (index 0) holds the final sum with Constant(7);
    // input-most layer (index 1) holds zero constant terms.
    assert_eq!(raw.layers[0].constant.num_terms(), 1);
    assert_eq!(raw.layers[1].constant.num_terms(), 0);

    let segmented = segment_circuit_v2(&fc, raw);
    let encoded = crate::core::proto::v2::CircuitWriter::new(&fc).to_bytes(&segmented);
    let (decoded, tail) = crate::core::proto::v2::CircuitReader::new(&fr)
        .from_bytes(&encoded)
        .unwrap();
    assert!(tail.is_empty());
    // (2 * 5) * 5 + 7 = 57 = 3 * 19.
    let inputs: Vec<_> = [2u64, 5, 5, 19]
        .into_iter()
        .map(|v| {
            fr.bytes_to_element(&fc.to_bytes(&fc.u64_to_element(v)))
                .unwrap()
        })
        .collect();
    crate::runtime::v2::sumcheck::eval_circuit(inputs.clone(), &decoded, &fr).unwrap();
    let mut bad = inputs;
    bad[3] = fr
        .bytes_to_element(&fc.to_bytes(&fc.u64_to_element(20)))
        .unwrap();
    assert!(crate::runtime::v2::sumcheck::eval_circuit(bad, &decoded, &fr).is_err());
}

#[test]
fn v2_product_assertions_keep_both_factors_and_debug_paths() {
    let fc = crate::compile::algebra::p256::P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let (raw, geometry, symbols) = compile_v2(&fc, |logic| {
        let x = logic.input(1);
        let y = logic.input(2);
        let z = logic.input(3);
        let expected = logic.input(4);
        let xy = logic.mul(&x, &y);
        let yx = logic.mul(&y, &x);
        let product = logic.assert0("product", &logic.mulk(&fc.u64_to_element(3), &xy));
        let alias = logic.assert0("alias", &logic.mulk(&fc.u64_to_element(5), &yx));
        let square = logic.mul(&z, &z);
        let fourth = logic.mul(&square, &square);
        let xyz = logic.mul(&xy, &z);
        let xyzz = logic.mul(&xy, &square);
        let value = logic.add(&fourth, &logic.add(&xyz, &xyzz));
        let deep = logic.assert_eq("deep", &value, &expected);
        (logic.assert_all("root", &[product, alias, deep]), 1)
    });
    // The scaled and swapped product checks share an assertion and preserve
    // both names. Its factors are needed earlier than the value constraint.
    assert_eq!(geometry.nassertions, 2);
    assert_eq!(symbols.assertion_count(), 2);
    let circuit = segment_circuit_v2(&fc, raw);
    let inputs = |values: [u64; 4]| {
        values.map(|v| {
            fr.bytes_to_element(&fc.to_bytes(&fc.u64_to_element(v)))
                .unwrap()
        })
    };
    for values in [[0, 7, 2, 16], [9, 0, 2, 16]] {
        eval_circuit_fc(&fc, &fr, &circuit, &symbols, &inputs(values))
            .unwrap()
            .assert_all_passed();
    }
    // With a nonzero product, both aliases fail while the separate value
    // constraint still evaluates 2^4 + (3*5)*2 + (3*5)*2^2 = 106.
    let mut product_failures =
        eval_circuit_fc(&fc, &fr, &circuit, &symbols, &inputs([3, 5, 2, 106]))
            .unwrap()
            .failed_paths();
    product_failures.sort_unstable();
    assert_eq!(product_failures, ["root/alias", "root/product"]);
    eval_circuit_fc(&fc, &fr, &circuit, &symbols, &inputs([0, 7, 2, 17]))
        .unwrap()
        .assert_any_failed_at("root/deep");
}

#[test]
fn v2_assertions_that_coalesce_during_copy_keep_both_paths() {
    let fc = crate::compile::algebra::p256::P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let (raw, geometry, symbols) = compile_v2(&fc, |logic| {
        let sum = logic.add(&logic.input(1), &logic.input(2));
        let plain = logic.assert0("plain", &sum);
        let precious = logic.assert0("precious", &logic.precious(&sum));
        (logic.assert_all("root", &[plain, precious]), 1)
    });
    assert_eq!(geometry.nassertions, 1);
    let circuit = segment_circuit_v2(&fc, raw);
    let one = fr
        .bytes_to_element(&fc.to_bytes(&fc.u64_to_element(1)))
        .unwrap();
    let mut failures = eval_circuit_fc(&fc, &fr, &circuit, &symbols, &[one; 2])
        .unwrap()
        .failed_paths();
    failures.sort_unstable();
    assert_eq!(failures, ["root/plain", "root/precious"]);
}

#[test]
fn v2_assertion_only_product_uses_one_layer() {
    let field = crate::compile::algebra::p256::P256Field::new();
    let (raw, geometry, _) = compile_v2(&field, |logic| {
        let product = logic.mul(&logic.input(1), &logic.input(2));
        (logic.assert0("product", &product), 1)
    });
    assert_eq!(geometry.nlayers, 1);
    assert_eq!(raw.layers[0].quadratic.num_terms(), 1);
}

#[test]
fn v2_unequal_depth_terms_preserve_nonunit_coefficients() {
    let fc = crate::compile::algebra::p256::P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let (raw, _, symbols) = compile_v2(&fc, |logic| {
        let x = logic.input(1);
        let y = logic.input(2);
        let z = logic.input(3);
        let expected = logic.input(4);
        let yz = logic.mul(&y, &z);
        let scaled_yz = logic.mulk(&fc.u64_to_element(7), &yz);
        let square = logic.mul(&yz, &yz);
        let fourth = logic.mul(&square, &square);
        let scaled_x = logic.mulk(&fc.u64_to_element(3), &x);
        let lower = logic.add(&scaled_x, &scaled_yz);
        let value = logic.add(&fourth, &lower);
        (logic.assert_eq("value", &value, &expected), 1)
    });
    let circuit = segment_circuit_v2(&fc, raw);
    for [x, y, z] in [[2u64, 3, 4], [5, 0, 7], [0, 2, 3]] {
        let yz = y * z;
        let value = yz.pow(4) + 7 * yz + 3 * x;
        let inputs = [x, y, z, value].map(|v| {
            fr.bytes_to_element(&fc.to_bytes(&fc.u64_to_element(v)))
                .unwrap()
        });
        eval_circuit_fc(&fc, &fr, &circuit, &symbols, &inputs)
            .unwrap()
            .assert_all_passed();
        let bad = [x, y, z, value + 1].map(|v| {
            fr.bytes_to_element(&fc.to_bytes(&fc.u64_to_element(v)))
                .unwrap()
        });
        eval_circuit_fc(&fc, &fr, &circuit, &symbols, &bad)
            .unwrap()
            .assert_any_failed_at("value");
    }
}
