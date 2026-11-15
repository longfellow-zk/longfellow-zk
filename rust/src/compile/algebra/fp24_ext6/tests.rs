// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Independent compile/runtime arithmetic and agreed encoding checks.
use super::CompileFp24Ext6;
use crate::{
    core::algebra::{
        encoding::FP24_EXT6,
        fp24::{BETA, EXTENSION_DEGREE, Q},
        AlgebraicField, FieldID, SerializableField, SupportsU64Conversions,
    },
    runtime::algebra::fp24_ext6::RuntimeFp24Ext6,
};
#[test]
fn compile_and_runtime_arithmetic_agree_on_the_wire() {
    let c = CompileFp24Ext6::new();
    let r = RuntimeFp24Ext6::new();
    for i in 1..80u32 {
        let a = std::array::from_fn(|j| (i * 997 + j as u32 * 131) % Q);
        let b = std::array::from_fn(|j| (Q - i + j as u32 * 257) % Q);
        let (ca, cb) = (c.from_coefficients(a), c.from_coefficients(b));
        let (ra, rb) = (r.from_coefficients(a), r.from_coefficients(b));
        for (compiler, runtime) in [
            (c.addf(&ca, &cb), r.addf(&ra, &rb)),
            (c.subf(&ca, &cb), r.subf(&ra, &rb)),
            (c.mulf(&ca, &cb), r.mulf(&ra, &rb)),
            (c.invert(&ca), r.invert(&ra)),
        ] {
            let bytes = c.to_bytes(&compiler);
            assert_eq!(bytes, r.to_bytes(&runtime));
            assert_eq!(
                FP24_EXT6.bytes_to_element(&bytes).unwrap().as_slice(),
                bytes
            );
            assert_eq!(c.bytes_to_element(&bytes).unwrap(), compiler);
        }
    }
}
#[test]
fn defining_relation_and_base_inversion() {
    let f = CompileFp24Ext6::new();
    let x = f.from_coefficients([0, 1, 0, 0, 0, 0]);
    let mut power = f.one();
    for _ in 0..EXTENSION_DEGREE {
        f.mul(&mut power, &x);
    }
    assert_eq!(power, f.u64_to_element(u64::from(BETA)));
    for i in [1, 2, 3, 7, Q - 2, Q - 1] {
        let a = f.u64_to_element(u64::from(i));
        assert_eq!(f.mulf(&a, &f.invert(&a)), f.one());
    }
}
#[test]
fn arithmetic_encoders_reject_aliases_in_each_coordinate() {
    let c = CompileFp24Ext6::new();
    let r = RuntimeFp24Ext6::new();
    for coordinate in 0..EXTENSION_DEGREE {
        let mut bytes = [0u8; 18];
        bytes[coordinate * 3..coordinate * 3 + 3].copy_from_slice(&Q.to_le_bytes()[..3]);
        assert!(c.bytes_to_element(&bytes).is_err());
        assert!(r.bytes_to_element(&bytes).is_err());
    }
    assert_eq!(c.to_bytes(&c.mone()), FP24_EXT6.serialized_mone());
    assert_eq!(r.to_bytes(&r.mone()), FP24_EXT6.serialized_mone());
}

#[test]
fn committed_pre_refactor_golden_values_are_preserved() {
    let c = CompileFp24Ext6::new();
    let r = RuntimeFp24Ext6::new();
    let a = [Q - 1, 2, 3, 4, 5, 6];
    let b = [7, 8, 9, 10, 11, 12];
    let product = [1323, 1294, 1169, 942, 607, 158];
    let inverse = [391404, 3903418, 2402230, 5070865, 6245190, 514490];
    assert_eq!(
        *c.mulf(&c.from_coefficients(a), &c.from_coefficients(b))
            .coefficients(),
        product
    );
    assert_eq!(
        *r.mulf(&r.from_coefficients(a), &r.from_coefficients(b))
            .coefficients(),
        product
    );
    assert_eq!(*c.invert(&c.from_coefficients(a)).coefficients(), inverse);
    assert_eq!(*r.invert(&r.from_coefficients(a)).coefficients(), inverse);
    assert_eq!(c.field_id(), FieldID::Fp24Ext6);
    assert_eq!(r.field_id(), FieldID::Fp24Ext6);
    assert_eq!(FP24_EXT6.field_id(), FieldID::Fp24Ext6);
}
