// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Freeze v1 bytes independently while checking the native v2 circuit semantics.
use sha2::{Digest, Sha256};

use crate::{
    compile::{
        algebra::field::CompileField,
        compiler::{
            compile_v1, compile_v2, segment_circuit, segment_circuit_v2, CompilerAssertions,
            CompilerLogic,
        },
        logic::{Logic, LogicIO},
    },
    core::{
        algebra::{SerializableField, SupportsU64Conversions},
        proto::{reader::CircuitReader, writer::CircuitWriter, FieldID},
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

fn check<const W: usize, FC, FR>(fc: &FC, fr: &FR, fid: FieldID, expected: [&str; 3])
where
    FC: CompileField + Clone + SupportsU64Conversions,
    FR: RuntimeField<W> + SerializableField,
{
    let (v1, g1, _) = compile_v1(fc, build);
    let (v2, g2, _) = compile_v2(fc, build);
    assert_eq!(g1.ninput, g2.ninput + 1);
    assert_eq!(g1.npublic_input, g2.npublic_input + 1);
    let writer = CircuitWriter::new(fc, fid);
    let legacy = segment_circuit(fc, &v1);
    let encodings = [
        writer.to_bytes_lfc1(&v1),
        writer.to_bytes_lfc2(&v1),
        writer.to_bytes_lfc2(&legacy),
    ];
    for (bytes, expected) in encodings.iter().zip(expected) {
        assert_eq!(
            format!("{:x}", Sha256::digest(bytes)),
            expected,
            "v1 serialization changed"
        );
        let (decoded, tail) = CircuitReader::new(fr, fid).from_bytes(bytes, true).unwrap();
        assert!(tail.is_empty());
        assert_eq!(decoded.id, v1.id);
    }
    let modern = segment_circuit_v2(fc, &v2);
    let encoded = writer.to_bytes_lfc3(&modern);
    let (modern, tail) = CircuitReader::new(fr, fid)
        .from_bytes_lfc3(&encoded, true)
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
        crate::runtime::sumcheck_v2::eval_circuit(inputs.clone(), &modern, fr).unwrap();
        let mut old = vec![fr.one()];
        old.extend(inputs.clone());
        crate::runtime::sumcheck_v1::eval_circuit(old.clone(), &legacy, fr).unwrap();
        for i in 8..16 {
            let mut bad = inputs.clone();
            fr.add(&mut bad[i], &fr.one());
            assert!(crate::runtime::sumcheck_v2::eval_circuit(bad, &modern, fr).is_err());
            let mut bad = old.clone();
            fr.add(&mut bad[i + 1], &fr.one());
            assert!(crate::runtime::sumcheck_v1::eval_circuit(bad, &legacy, fr).is_err());
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
