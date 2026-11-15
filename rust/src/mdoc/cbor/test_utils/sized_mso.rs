// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Sized benchmark credentials. TEST ONLY: issuer private key and nonce are both
//! one. The original device signature remains valid because its transcript and
//! device key are unchanged. Never use this issuer or signer for real documents.
use sha2::{Digest, Sha256};

use crate::{
    core::algebra::{ec::Curve, AlgebraicField, Nat, SupportsNatConversions},
    mdoc::cbor::{
        append_bytes_len, encode_cbor_string,
        mdoc::format_cose_sign1_message,
        parse::{CborElement, CborParser, CborValue},
    },
    runtime::algebra::{p256::P256Field, q256::Q256Field, secp256r1::Secp256r1, RuntimeNat},
};

fn get<'a>(map: &'a CborElement, key: &str) -> &'a CborElement {
    let CborValue::Map(entries) = &map.value else {
        panic!("fixture map");
    };
    &entries
        .iter()
        .find(|(k, _)| matches!(&k.value, CborValue::Text(name) if name == key))
        .unwrap()
        .1
}

fn bytes(value: &[u8]) -> Vec<u8> {
    let mut result = Vec::new();
    append_bytes_len(&mut result, value.len());
    result.extend_from_slice(value);
    result
}

pub fn with_mso_size(source: &[u8], target: usize) -> Result<(Vec<u8>, (String, String)), String> {
    let root = CborParser::new(source).parse_exact()?;
    let CborValue::Array(documents) = &get(&root, "documents").value else {
        return Err("documents".into());
    };
    let tagged_auth = get(get(&documents[0], "issuerSigned"), "issuerAuth");
    let auth = if let CborValue::Tag(_, inner) = &tagged_auth.value {
        inner.as_ref()
    } else {
        tagged_auth
    };
    let CborValue::Array(cose) = &auth.value else {
        return Err("issuerAuth".into());
    };
    let CborValue::Bytes(payload) = &cose[2].value else {
        return Err("issuer payload".into());
    };
    let tagged_payload = CborParser::new(payload).parse_exact()?;
    let CborValue::Tag(24, inner) = &tagged_payload.value else {
        return Err("MSO tag".into());
    };
    let CborValue::Bytes(raw) = &inner.value else {
        return Err("MSO bytes".into());
    };
    let map = CborParser::new(raw).parse_exact()?;
    let CborValue::Map(entries) = &map.value else {
        return Err("MSO map".into());
    };
    if entries.len() >= 23 || raw[0] != 0xa0 + entries.len() as u8 {
        return Err("fixture map header".into());
    }
    let mut prefix = vec![raw[0] + 1];
    prefix.extend_from_slice(&raw[1..]);
    prefix.extend_from_slice(&encode_cbor_string(b"structuralPadding"));
    let padding = (0..=target)
        .find(|n| prefix.len() + bytes(&vec![0; *n]).len() == target)
        .ok_or("target MSO too short")?;
    let mut resized = prefix;
    resized.extend_from_slice(&bytes(&vec![0; padding]));
    let mut tagged = vec![0xd8, 0x18];
    tagged.extend_from_slice(&bytes(&resized));
    let message = format_cose_sign1_message(&tagged);
    let digest = Sha256::digest(&message);
    let f = P256Field::new();
    let q = Q256Field::new();
    let curve = Secp256r1::new(&f);
    let gx: RuntimeNat<4> = f.to_nat(&curve.g().0);
    let gy: RuntimeNat<4> = f.to_nat(&curve.g().1);
    let r = q.reduce_nat(&gx);
    let z = q.reduce_nat(&RuntimeNat::<4>::from_bytes_be(&digest));
    let s = q.addf(&z, &r); // k=d=1: s = z+r (mod curve order).
    let mut signature = Vec::new();
    for scalar in [&r, &s] {
        let mut encoded = q.to_nat(scalar).to_bytes_le();
        encoded.resize(32, 0);
        encoded.reverse();
        signature.extend_from_slice(&encoded);
    }
    let mut output = source.to_vec();
    output.splice(cose[3].start..cose[3].end, bytes(&signature));
    output.splice(cose[2].start..cose[2].end, bytes(&tagged));
    let hex = |n: &RuntimeNat<4>| {
        format!(
            "0x{}",
            num_bigint::BigUint::from_bytes_le(&n.to_bytes_le()).to_str_radix(16)
        )
    };
    Ok((output, (hex(&gx), hex(&gy))))
}
