// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! V2 input capacity and early rejection, without compiling a circuit.
use crate::{
    mdoc::v2::{
        req_attr, run_mdoc_prover_inner, run_mdoc_verifier, MdocProverErrorCode,
        MdocVerifierErrorCode,
    },
    runtime::random::DeterministicRng,
};

#[test]
fn rejects_invalid_public_inputs_before_loading_or_sampling() {
    let spec = &crate::mdoc::runtime::tests_specs::v2_spec();
    let valid = req_attr("namespace", "a", [0xf5]);
    let now = "2026-10-23T00:00:00Z";
    let mut long_id = valid.clone();
    long_id.id = vec![b'a'; 31]; // CBOR header plus text exceeds the 32-byte slot.
    let mut long_value = valid.clone();
    long_value.cbor_value = crate::mdoc::circuits::cbor::encode_cbor_string(&[b'a'; 63]);
    let mut nested_value = valid.clone();
    nested_value.cbor_value = vec![0xc0; 100_000];
    nested_value.cbor_value.push(0x00);
    let long_doc = "x".repeat(33);
    let long_now = format!("{now}x");
    for (attrs, time, doc_type) in [
        (vec![], now, "doc"),
        (vec![valid.clone(), valid.clone()], now, "doc"),
        (vec![long_id], now, "doc"),
        (vec![long_value], now, "doc"),
        (vec![nested_value], now, "doc"),
        (vec![valid.clone()], &now[..19], "doc"),
        (vec![valid.clone()], long_now.as_str(), "doc"),
        (vec![valid.clone()], now, long_doc.as_str()),
    ] {
        let mut rng = DeterministicRng::new(42);
        // Deliberately invalid circuit and document bytes: validation must run first.
        assert_eq!(
            run_mdoc_prover_inner(
                spec,
                &[],
                &[],
                "0",
                "0",
                b"inputs",
                &attrs,
                time,
                doc_type,
                &mut rng,
            ),
            Err(MdocProverErrorCode::InvalidInput)
        );
        assert_eq!(
            rng.state, 42,
            "invalid inputs must not consume prover randomness"
        );
        let expected = if attrs.len() == spec.num_attributes {
            MdocVerifierErrorCode::InvalidInput
        } else {
            MdocVerifierErrorCode::AttributeNumberMismatch
        };
        assert_eq!(
            run_mdoc_verifier(spec, &[], "0", "0", b"inputs", &attrs, time, doc_type, &[],),
            Err(expected)
        );
    }
    let boundary = req_attr(
        "namespace",
        [b'a'; 30],
        crate::mdoc::circuits::cbor::encode_cbor_string(&[b'a'; 62]),
    );
    assert!(super::public_inputs_fit(
        &[boundary],
        now.as_bytes(),
        &[b'x'; 32]
    ));
}

#[test]
fn private_hash_inputs_enforce_sha_capacity() {
    use crate::mdoc::{
        circuits::cbor::mdoc::parse_mdoc,
        proto::{
            hash::constants::K_MSO_PREIMAGE_LEN, mso_attribute::constants::K_MAX_ATTR_CBOR_LEN,
        },
    };
    let fixture = &crate::mdoc::testcases::vectors::BIRTHDATE_1971_09_01_MDOC_3;
    let mut parsed = parse_mdoc::<crate::runtime::algebra::RuntimeNat<4>>(
        fixture.mdoc,
        fixture.transcript,
        "org.iso.18013.5.1.mDL",
    )
    .unwrap();
    let attribute = &parsed.attrs[0];
    let request = [req_attr(
        "org.iso.18013.5.1",
        &attribute.name,
        &attribute.cbor_value,
    )];
    let field = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
    for length in [K_MAX_ATTR_CBOR_LEN, K_MAX_ATTR_CBOR_LEN + 1, 255, 256] {
        parsed.attrs[0].cbor_issuer_signed_item = vec![0; length];
        let result = super::push_witness_hash_boolean(&field, &request, &parsed, &[[0; 2]; 3]);
        if length == K_MAX_ATTR_CBOR_LEN {
            assert!(result.is_ok());
        } else {
            assert_eq!(result, Err(MdocProverErrorCode::AttributeTooLong));
        }
    }
    parsed.cbor_mso = vec![0; K_MSO_PREIMAGE_LEN];
    assert_eq!(
        super::push_witness_hash_boolean(&field, &request, &parsed, &[[0; 2]; 3]),
        Err(MdocProverErrorCode::TaggedMsoTooBig),
    );
}
