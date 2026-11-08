// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    compile::algebra::{p256::P256Field, q256::Q256Field, secp256r1::Secp256r1, CompileNat},
    core::algebra::{AlgebraicField, SerializableField},
};

#[test]
fn checked_constructors_preserve_existing_witness_bytes() {
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    let nat = |value: &str| CompileNat::<4>::from_bytes_be(&hex::decode(value).unwrap());
    let pk_nat = (
        nat("88903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaaf686c8f9ff5e7c6368d9c"),
        nat("eb8341fc38bb802138498d5f4c03733f457ebbafd0b2fe38e6f58626767f9e75"),
    );
    let pk = (f.reduce_nat(&pk_nat.0), f.reduce_nat(&pk_nat.1));
    let e = &nat("2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae");
    let r = &nat("00c71bcbfb28bbe06299a225f057797aaf5f22669e90475de5f64176b2612671");
    let s = &nat("42ad2f2ec7b6e91360b53427690dddfe578c10d8cf480a66a6c2410ff4f6dd40");
    let old_given = given(&curve, &pk, e, r, s, &f, &q);
    let old_derived = derived(&curve, &pk, e, r, s, &f, &q);
    let new_given = try_given(&curve, &pk, e, r, s, &f, &q).unwrap();
    let new_derived = try_derived(&curve, &pk, e, r, s, &f, &q).unwrap();
    let mut old = Vec::new();
    let mut new = Vec::new();
    old_given.push_elements(|value| old.extend(f.to_bytes(value)));
    old_derived.push_elements(|value| old.extend(f.to_bytes(value)));
    new_given.push_elements(|value| new.extend(f.to_bytes(value)));
    new_derived.push_elements(|value| new.extend(f.to_bytes(value)));
    assert_eq!(old, new);
    let (combined_given, combined_derived) = try_witness(&curve, &pk, e, r, s, &f, &q).unwrap();
    let mut combined = Vec::new();
    combined_given.push_elements(|value| combined.extend(f.to_bytes(value)));
    combined_derived.push_elements(|value| combined.extend(f.to_bytes(value)));
    assert_eq!(old, combined);
}

#[test]
fn valid_negative_generator_key_and_zero_signature_return_errors() {
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    let generator = curve.g();
    let pk = (generator.0.clone(), f.neg(&generator.1));
    let e = CompileNat::<4>::from_u64(555555555);
    let r = f.to_nat(&generator.0);
    // Sign with private key -1 and nonce 1: R=G, s=e-r (mod n).
    let s = q.to_nat(&q.subf(&q.reduce_nat(&e), &q.reduce_nat(&r)));
    assert!(try_given(&curve, &pk, &e, &r, &s, &f, &q).is_ok());
    assert!(try_derived(&curve, &pk, &e, &r, &s, &f, &q).is_err());
    assert!(try_witness(&curve, &pk, &e, &r, &s, &f, &q).is_err());
    let zero = CompileNat::<4>::from_u64(0);
    assert!(try_given(&curve, &pk, &e, &r, &zero, &f, &q).is_err());
    assert!(try_derived(&curve, &pk, &e, &r, &zero, &f, &q).is_err());
    assert!(try_witness(&curve, &pk, &e, &r, &zero, &f, &q).is_err());
}
