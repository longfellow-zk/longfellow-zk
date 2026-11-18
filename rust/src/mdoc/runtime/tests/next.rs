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

//! Longfellow v2 application compatibility and failure cases.

use crate::{
    compile::algebra::CompileNat,
    core::{
        algebra::Nat,
        proto::{
            archive::{CircuitArchive, CircuitArchiveBuilder},
            v2::CircuitReader,
        },
    },
    mdoc::{
        cbor::{mdoc::ParsedMdoc, test_utils::parse_test_data},
        development_provider::tests::fixtures::next_circuit,
        proto::{layout::public, NEXT_VERSION},
        runtime::v2::run_mdoc_prover_encoded,
        testcases::{ALL_TEST_CASES, TEST_DATA},
        v2::{
            decompress_circuits, find_zk_spec, link_for_test, proof_geometry, provider, req_attr,
            run_mdoc_prover_inner, run_mdoc_verifier, MdocProverErrorCode, MdocVerifierErrorCode,
            RequestedAttribute, ZkSpecStruct, SYSTEM_ID,
        },
    },
    runtime::{random::DeterministicRng, v2::proto::polygero::PolygeroConfig},
};

/// The NEXT circuits of one to four attributes. Each test loads its own
/// copy; they share one compilation per circuit through the test cache.
struct TestCircuits {
    circuits: std::collections::HashMap<usize, provider::ProvidedCircuit>,
}

impl TestCircuits {
    fn load() -> Self {
        let circuits = (1..=4).map(|count| (count, next_circuit(count))).collect();
        Self { circuits }
    }

    fn get(&self, nattrs: usize) -> Option<&provider::ProvidedCircuit> {
        self.circuits.get(&nattrs)
    }
}

#[test]
fn next_mdoc_flow() {
    let test_circuits = &TestCircuits::load();
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = TEST_DATA.mdoc;
    let transcript = TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";

    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let provided = test_circuits.get(req_attrs.len()).unwrap();

    let mut rng = DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        provided.spec(),
        provided.compressed(),
        mdoc_bytes,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &mut rng,
    )
    .unwrap();

    assert_eq!(&zkproof[..4], b"MDA7");
    assert_eq!(SYSTEM_ID, crate::mdoc::LONGFELLOW_V2);

    let verify_res = run_mdoc_verifier(
        provided.spec(),
        provided.compressed(),
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &zkproof,
    );
    assert!(
        verify_res.is_ok(),
        "Verification failed: {:?}",
        verify_res.err()
    );
    let mut renamed = req_attrs.clone();
    for attribute in &mut renamed {
        attribute.namespace_id = b"unrelated.namespace".to_vec();
    }
    assert!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &renamed,
            now,
            doc_type,
            &zkproof,
        )
        .is_err(),
        "the same proof must not verify under a different namespace"
    );
    assert_eq!(
        run_mdoc_prover_inner(
            provided.spec(),
            provided.compressed(),
            mdoc_bytes,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &renamed,
            now,
            doc_type,
            &mut rng,
        ),
        Err(MdocProverErrorCode::NamespacesMissing)
    );
}

#[test]
fn next_mdoc_subset_flow() {
    let test_circuits = &TestCircuits::load();
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .step_by(2)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = TEST_DATA.mdoc;
    let transcript = TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";

    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let provided = test_circuits.get(req_attrs.len()).unwrap();

    let mut rng = DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        provided.spec(),
        provided.compressed(),
        mdoc_bytes,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &mut rng,
    )
    .unwrap();

    assert!(!zkproof.is_empty());

    let verify_res = run_mdoc_verifier(
        provided.spec(),
        provided.compressed(),
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &zkproof,
    );
    assert!(
        verify_res.is_ok(),
        "Verification failed: {:?}",
        verify_res.err()
    );
}

// A document type does not determine the namespace: mDL fixtures can disclose
// AAMVA attributes. Derive the request without skipping any disclosed attribute.
fn requested_fixture_attributes(
    parsed: &ParsedMdoc<CompileNat<4>>,
    case_name: &str,
) -> Vec<RequestedAttribute> {
    let namespaces = parsed.namespaces().unwrap();
    let namespace = namespaces
        .iter()
        .find(|namespace| {
            parsed.attrs.iter().all(|attribute| {
                namespace
                    .digest_range
                    .contains(&attribute.mso_digest_offset_in_preimage)
            })
        })
        .unwrap_or_else(|| {
            panic!("Fixture does not have one global disclosure namespace: {case_name}")
        });
    parsed
        .attrs
        .iter()
        .map(|attribute| req_attr(&namespace.name, &attribute.name, &attribute.cbor_value))
        .collect()
}

#[test]
fn next_mdoc_all_positive_cases() {
    let test_circuits = &TestCircuits::load();
    for case in ALL_TEST_CASES {
        if case.name.starts_with("fail-") {
            continue;
        }
        let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(case.data);
        let nattrs = parsed.attrs.len();
        if nattrs == 0 || nattrs > 4 {
            continue;
        }
        let req_attrs = requested_fixture_attributes(&parsed, case.name);

        if !crate::mdoc::v2::same_namespace(&req_attrs) {
            continue;
        }
        if req_attrs
            .iter()
            .any(|a| !crate::mdoc::v2::circuit_supports(&a.cbor_value))
        {
            continue;
        }

        let Some(provided) = test_circuits.get(nattrs) else {
            continue;
        };

        let mut rng = DeterministicRng::new(42);

        let zkproof = run_mdoc_prover_inner(
            provided.spec(),
            provided.compressed(),
            case.data.mdoc,
            case.data.pkx,
            case.data.pky,
            case.data.transcript,
            &req_attrs,
            now,
            case.data.doc_type,
            &mut rng,
        )
        .unwrap_or_else(|_| panic!("Prover failed for positive case: {}", case.name));

        assert!(!zkproof.is_empty(), "Proof empty for {}", case.name);

        let verify_res = run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            case.data.pkx,
            case.data.pky,
            case.data.transcript,
            &req_attrs,
            now,
            case.data.doc_type,
            &zkproof,
        );
        assert!(
            verify_res.is_ok(),
            "Verifier failed for positive case {}: {:?}",
            case.name,
            verify_res.err()
        );
    }
}

#[test]
fn next_mdoc_all_negative_cases() {
    let test_circuits = &TestCircuits::load();
    let mut executed = 0;
    let mut skipped_for_attribute_count = Vec::new();
    for case in ALL_TEST_CASES {
        if !case.name.starts_with("fail-") {
            continue;
        }
        let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(case.data);
        let nattrs = parsed.attrs.len();
        assert_ne!(
            nattrs, 0,
            "negative vector unexpectedly contains no attributes: {}",
            case.name
        );
        if nattrs > 4 {
            skipped_for_attribute_count.push(case.name);
            continue;
        }
        let mut req_attrs = requested_fixture_attributes(&parsed, case.name);

        if case.name.contains("not_over_18") {
            for a in &mut req_attrs {
                if a.id == b"age_over_18" {
                    a.cbor_value = vec![0xf4]; // boolean false
                }
            }
        } else if case.name.contains("0971_09_01") {
            for a in &mut req_attrs {
                if a.id == b"birth_date" {
                    a.cbor_value = vec![
                        0xD9, 0x03, 0xEC, 0x6A, b'0', b'9', b'7', b'1', b'-', b'0', b'9', b'-',
                        b'0', b'1',
                    ];
                }
            }
        } else if case.name.contains("1871_09_01") {
            for a in &mut req_attrs {
                if a.id == b"birth_date" {
                    a.cbor_value = vec![
                        0xD9, 0x03, 0xEC, 0x6A, b'1', b'8', b'7', b'1', b'-', b'0', b'9', b'-',
                        b'0', b'1',
                    ];
                }
            }
        } else if case.name.contains("extra_0") {
            for a in &mut req_attrs {
                if a.id == b"birth_date" {
                    a.cbor_value = vec![
                        0xD9, 0x03, 0xEC, 0x6A, b'1', b'9', b'7', b'1', b'-', b'0', b'9', b'-',
                        b'0', b'1', b'0',
                    ];
                }
            }
        }

        let provided = test_circuits
            .get(nattrs)
            .unwrap_or_else(|| panic!("missing {nattrs}-attribute circuit for {}", case.name));

        let mut rng = DeterministicRng::new(42);

        let zkproof_res = run_mdoc_prover_inner(
            provided.spec(),
            provided.compressed(),
            case.data.mdoc,
            case.data.pkx,
            case.data.pky,
            case.data.transcript,
            &req_attrs,
            now,
            case.data.doc_type,
            &mut rng,
        );
        assert_eq!(
            zkproof_res,
            Err(MdocProverErrorCode::GeneralFailure),
            "wrong prover failure for negative case: {}",
            case.name
        );
        assert_eq!(rng.state, 42, "{} must fail before sampling", case.name);
        executed += 1;
    }

    assert_eq!(
        skipped_for_attribute_count,
        [
            "fail-birthdate_0971_09_01-mdoc[3].json",
            "fail-birthdate_1871_09_01-mdoc[3].json",
            "fail-birthdate_1971_09_01_extra_0-mdoc[3].json",
        ],
        "the current API supports at most four attributes; every other negative vector must execute"
    );
    assert_eq!(executed, 3, "unexpected negative-vector coverage");
}

#[test]
fn next_verifier_negative_cases() {
    let test_circuits = &TestCircuits::load();
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = TEST_DATA.mdoc;
    let transcript = TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";

    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let provided = test_circuits.get(req_attrs.len()).unwrap();
    let mut rng = DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        provided.spec(),
        provided.compressed(),
        mdoc_bytes,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &mut rng,
    )
    .unwrap();

    // 1. Wrong PKX
    let invalid_key_x_string = "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef";
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            invalid_key_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong PKX"
    );

    // 2. Wrong PKY
    let invalid_key_y_formatted =
        "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef";
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            invalid_key_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong PKY"
    );

    // 3. Wrong Transcript: still one CBOR item, so it passes the request
    // check, but byte 5 changes the case of the first letter of the handover
    // type text, "BrowserHandover".
    let mut bad_transcript = transcript.to_vec();
    assert_eq!(&bad_transcript[3..6], &[0x84, 0x71, b'B']);
    bad_transcript[5] ^= 0x20;
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            &bad_transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong transcript"
    );

    // 4. Wrong Timestamp
    let bad_now = "2099-01-01T00:00:00Z";
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            bad_now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong timestamp"
    );

    // 5. Wrong Doc Type
    let bad_doc_type = "org.iso.18013.5.1.fake";
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            bad_doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong doc_type"
    );

    // 6. Empty Doc Type
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            "",
            &zkproof
        ),
        Err(MdocVerifierErrorCode::InvalidInput),
        "Verifier should reject empty doc_type"
    );

    // 7. Attribute Mismatch - Wrong Value
    let mut bad_attrs_val = req_attrs.clone();
    bad_attrs_val[0].cbor_value = vec![0x63, b'f', b'o', b'o']; // Text "foo"
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &bad_attrs_val,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong attribute value"
    );

    // 8. Attribute Mismatch - Wrong ID
    let mut bad_attrs_id = req_attrs.clone();
    bad_attrs_id[0].id = vec![b'x'];
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &bad_attrs_id,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong attribute id"
    );

    // 9. Attribute Number Mismatch - Too Few
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &[],
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject empty attributes slice"
    );

    // 10. Attribute Number Mismatch - Too Many
    let mut two_attrs = req_attrs.clone();
    two_attrs.push(req_attrs[0].clone());
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &two_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject too many attributes"
    );

    // 11. Unsupported ZkSpec Version (version 0 and version 99)
    let mut bad_spec_0 = *provided.spec();
    bad_spec_0.version = 0;
    assert_eq!(
        run_mdoc_verifier(
            &bad_spec_0,
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::InvalidZkSpecVersion),
        "Verifier should reject version 0"
    );

    let mut bad_spec_99 = *provided.spec();
    bad_spec_99.version = 99;
    assert_eq!(
        run_mdoc_verifier(
            &bad_spec_99,
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::InvalidZkSpecVersion),
        "Verifier should reject version 99"
    );

    // Requested values must be single, complete, supported CBOR items: the
    // hash circuit matches raw value bytes, so this guard rejects prefixes.
    for unsupported in [&[0x82, 0x01, 0x02][..], &[0x65, 0x61][..]] {
        let mut requested = req_attrs.clone();
        requested[0].cbor_value = unsupported.to_vec();
        assert_eq!(
            run_mdoc_verifier(
                provided.spec(),
                provided.compressed(),
                &pubkey_x_string,
                &pubkey_y_formatted,
                transcript,
                &requested,
                now,
                doc_type,
                &zkproof
            ),
            Err(MdocVerifierErrorCode::UnsupportedAttribute),
            "Verifier should reject unsupported value {unsupported:02x?}"
        );
    }
}

#[test]
fn next_verifier_attribute_reordering_and_duplicates() {
    let test_circuits = &TestCircuits::load();
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let all_req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let two_attrs = if all_req_attrs.len() >= 2 {
        vec![all_req_attrs[0].clone(), all_req_attrs[1].clone()]
    } else {
        let mut second = all_req_attrs[0].clone();
        second.id = b"fake_attr".to_vec();
        vec![all_req_attrs[0].clone(), second]
    };

    let mdoc_bytes = TEST_DATA.mdoc;
    let transcript = TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";
    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let provided = test_circuits.get(2).unwrap();
    let mut rng = DeterministicRng::new(42);
    let zkproof_res = run_mdoc_prover_inner(
        provided.spec(),
        provided.compressed(),
        mdoc_bytes,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &two_attrs,
        now,
        doc_type,
        &mut rng,
    );
    let zkproof =
        zkproof_res.expect("prover must succeed before verifier attribute-order corruptions");

    let reordered = vec![two_attrs[1].clone(), two_attrs[0].clone()];
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &reordered,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject reordered attributes"
    );

    let duplicates = vec![two_attrs[0].clone(), two_attrs[0].clone()];
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &duplicates,
            now,
            doc_type,
            &zkproof
        ),
        Err(MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject duplicate attributes"
    );
}

#[test]
fn next_verifier_bad_proofs() {
    let test_circuits = &TestCircuits::load();
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = TEST_DATA.mdoc;
    let transcript = TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";
    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let provided = test_circuits.get(req_attrs.len()).unwrap();
    let mut rng = DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        provided.spec(),
        provided.compressed(),
        mdoc_bytes,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &mut rng,
    )
    .unwrap();

    // 1. Empty proof
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &[]
        ),
        Err(MdocVerifierErrorCode::HashParsingFailure),
        "Verifier should reject empty proof"
    );

    // 2. Random bytes of various lengths
    for len in [10, 100, 1000, 5000, 10000, 20000] {
        let random_bytes: Vec<u8> = (0..len)
            .map(|i| u8::try_from(i * 37 % 256).unwrap())
            .collect();
        assert_eq!(
            run_mdoc_verifier(
                provided.spec(),
                provided.compressed(),
                &pubkey_x_string,
                &pubkey_y_formatted,
                transcript,
                &req_attrs,
                now,
                doc_type,
                &random_bytes
            ),
            Err(MdocVerifierErrorCode::HashParsingFailure),
            "Verifier should reject random proof of len {len}"
        );
    }

    // 3. Bit/byte flips in valid proof
    for idx in [10, 100, zkproof.len() / 2, zkproof.len().saturating_sub(10)] {
        if idx < zkproof.len() {
            let mut flipped = zkproof.clone();
            flipped[idx] ^= 0x55;
            assert_eq!(
                run_mdoc_verifier(
                    provided.spec(),
                    provided.compressed(),
                    &pubkey_x_string,
                    &pubkey_y_formatted,
                    transcript,
                    &req_attrs,
                    now,
                    doc_type,
                    &flipped
                ),
                Err(MdocVerifierErrorCode::GeneralFailure),
                "Verifier should reject proof with byte flip at index {idx}"
            );
        }
    }

    // The application accepts only the joint envelope, never two old standalone proofs.
    for marker in [
        b"LFV5", b"LFV6", b"MJP1", b"MJP2", b"MDA1", b"MDA2", b"MDA3", b"MDA6",
    ] {
        let mut obsolete = zkproof.clone();
        obsolete[..4].copy_from_slice(marker);
        assert_eq!(
            run_mdoc_verifier(
                provided.spec(),
                provided.compressed(),
                &pubkey_x_string,
                &pubkey_y_formatted,
                transcript,
                &req_attrs,
                now,
                doc_type,
                &obsolete,
            ),
            Err(MdocVerifierErrorCode::HashParsingFailure)
        );
    }

    // Masked quotients follow the magic, root, both fingerprints, the split
    // sumcheck and mu (send order). A data bit flip must fail verification;
    // a padding bit must fail decoding.
    let split_sumcheck = {
        use crate::runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field};
        let (sig, hash) = decompress_circuits(
            provided.compressed(),
            &P256Field::new(),
            &Gf2_128Field::new(),
        )
        .unwrap();
        let geometry = proof_geometry(provided.spec(), &sig, &hash).unwrap();
        32 * geometry.body.split().sumcheck().serialized_elements()
    };
    let masked_at = 4 + 32 + 32 + 64 + split_sumcheck + 32;
    for (byte, bit, expected) in [
        (0, 0, MdocVerifierErrorCode::GeneralFailure),
        (3, 1, MdocVerifierErrorCode::GeneralFailure),
        (1, 7, MdocVerifierErrorCode::HashParsingFailure),
    ] {
        let mut tampered = zkproof.clone();
        tampered[masked_at + byte] ^= 1 << bit;
        assert_eq!(
            run_mdoc_verifier(
                provided.spec(),
                provided.compressed(),
                &pubkey_x_string,
                &pubkey_y_formatted,
                transcript,
                &req_attrs,
                now,
                doc_type,
                &tampered,
            ),
            Err(expected),
            "masked quotient byte {byte} bit {bit}"
        );
    }

    // 4. Truncated proof
    if zkproof.len() > 100 {
        let truncated = &zkproof[..zkproof.len() - 100];
        assert_eq!(
            run_mdoc_verifier(
                provided.spec(),
                provided.compressed(),
                &pubkey_x_string,
                &pubkey_y_formatted,
                transcript,
                &req_attrs,
                now,
                doc_type,
                truncated
            ),
            Err(MdocVerifierErrorCode::HashParsingFailure),
            "Verifier should reject truncated proof"
        );
    }

    // 5. Extended proof with trailing garbage
    let mut extended = zkproof.clone();
    extended.extend_from_slice(&[0xaa; 100]);
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &extended
        ),
        Err(MdocVerifierErrorCode::HashParsingFailure),
        "Verifier should reject proof with trailing garbage"
    );
}

#[test]
fn circuit_supports_cbor() {
    use crate::mdoc::v2::circuit_supports;

    // Valid Inputs (ported from C++ CborValidate.ValidInputs)
    assert!(circuit_supports(&[0x00]), "Integer 0");
    assert!(circuit_supports(&[0x01]), "Integer 1");
    assert!(circuit_supports(&[0x20]), "Integer -1");
    assert!(circuit_supports(&[0xF5]), "Boolean True");
    assert!(circuit_supports(&[0xF4]), "Boolean False");
    assert!(circuit_supports(&[0x60]), "Empty String");
    assert!(circuit_supports(&[0x61, b'a']), "String 'a'");
    assert!(circuit_supports(&[0x40]), "Empty Bytes");
    assert!(circuit_supports(&[0x41, 0x01]), "Bytes 0x01");

    // Fulldate: Tag 1004 (D9 03 EC) + String (6A) + 10 bytes -> 14 bytes
    let mut fulldate = vec![0xD9, 0x03, 0xEC, 0x6A];
    fulldate.extend_from_slice(&[b'0'; 10]);
    assert_eq!(fulldate.len(), 14);
    assert!(circuit_supports(&fulldate), "Fulldate 14 bytes");

    // Tdate: Tag 0 (C0) + String (74, len 20) + 20 bytes -> 22 bytes
    let mut tdate = vec![0xC0, 0x74];
    tdate.extend_from_slice(&[b'0'; 20]);
    assert_eq!(tdate.len(), 22);
    assert!(circuit_supports(&tdate), "Tdate 22 bytes");

    // Invalid Inputs (ported from C++ CborValidate.InvalidInputs)
    assert!(!circuit_supports(&[]), "Empty slice");
    assert!(!circuit_supports(&[0x80]), "Array not allowed");
    assert!(!circuit_supports(&[0xA0]), "Map not allowed");
    assert!(
        !circuit_supports(&[0x61]),
        "Malformed length (missing data)"
    );
    assert!(
        !circuit_supports(&[0xF5, 0xF5]),
        "Boolean with trailing data"
    );
    assert!(!circuit_supports(&[0xC2, 0x40]), "Unsupported Tag 2");

    // Fulldate wrong lengths (expected 14)
    let mut fulldate_wrong = vec![0xD9, 0x03, 0xEC, 0x69]; // String len 9
    fulldate_wrong.extend_from_slice(&[b'0'; 9]);
    assert_eq!(fulldate_wrong.len(), 13);
    assert!(!circuit_supports(&fulldate_wrong), "Fulldate len 13");
    fulldate_wrong.extend_from_slice(&[b'0'; 2]);
    assert!(!circuit_supports(&fulldate_wrong), "Fulldate len 15");
    fulldate_wrong.extend_from_slice(&[b'0'; 7]);
    assert!(!circuit_supports(&fulldate_wrong), "Fulldate len 22");

    // Fulldate inner type mismatch (Tag 1004 + Integer 0)
    assert!(
        !circuit_supports(&[0xD9, 0x03, 0xEC, 0x00]),
        "Fulldate inner integer"
    );

    // Tdate wrong lengths (expected 22)
    let mut tdate_short = vec![0xC0, 0x73]; // String len 19
    tdate_short.extend_from_slice(&[b'0'; 19]);
    assert_eq!(tdate_short.len(), 21);
    assert!(!circuit_supports(&tdate_short), "Tdate len 21");

    // Tdate inner type mismatch (Tag 0 + Integer 0)
    assert!(!circuit_supports(&[0xC0, 0x00]), "Tdate inner integer");

    // Trailing garbage after valid integer
    assert!(
        !circuit_supports(&[0x01, 0x01]),
        "Valid integer followed by garbage"
    );
}

#[test]
fn namespace_mixup() {
    use crate::mdoc::v2::{req_attr, same_namespace};

    let test_circuits = &TestCircuits::load();
    let attr1 = req_attr("org.iso.18013.5.1", "family_name", [0x63, b'f', b'o', b'o']);
    let attr2 = req_attr("org.iso.18013.5.1", "birth_date", [0x63, b'b', b'a', b'r']);
    let attr3 = req_attr(
        "aamva.test.namespace",
        "family_name",
        [0x63, b'b', b'a', b'z'],
    );

    assert!(
        same_namespace(&[attr1.clone(), attr2.clone()]),
        "Same namespace should be true"
    );
    assert!(
        !same_namespace(&[attr1.clone(), attr3.clone()]),
        "Mixed namespace should be false"
    );

    let (issuer_pk, _, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let provided = test_circuits.get(2).unwrap();
    let mixed_attrs = vec![attr1, attr3];

    let res = run_mdoc_verifier(
        provided.spec(),
        provided.compressed(),
        &pubkey_x_string,
        &pubkey_y_formatted,
        TEST_DATA.transcript,
        &mixed_attrs,
        now,
        "org.iso.18013.5.1.mDL",
        &[0u8; 1000],
    );
    assert_eq!(
        res,
        Err(MdocVerifierErrorCode::InvalidInput),
        "Verifier should reject mixed namespace"
    );
}

/// The rows of the error table in `mdoc/runtime/v2/DESIGN.md` that need real
/// circuits, in both roles where they apply; `v2::request::tests` checks the
/// request rows without circuits.
#[test]
fn next_error_table() {
    let test_circuits = &TestCircuits::load();
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let req_attrs = requested_fixture_attributes(&parsed, "TEST_DATA");
    let doc_type = "org.iso.18013.5.1.mDL";
    let pkx = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pky = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );
    let provided = test_circuits.get(req_attrs.len()).unwrap();
    let prove = |spec: &ZkSpecStruct, compressed: &[u8]| {
        run_mdoc_prover_inner(
            spec,
            compressed,
            TEST_DATA.mdoc,
            &pkx,
            &pky,
            TEST_DATA.transcript,
            &req_attrs,
            now,
            doc_type,
            &mut DeterministicRng::new(42),
        )
    };
    let verify = |spec: &ZkSpecStruct, compressed: &[u8], proof: &[u8]| {
        run_mdoc_verifier(
            spec,
            compressed,
            &pkx,
            &pky,
            TEST_DATA.transcript,
            &req_attrs,
            now,
            doc_type,
            proof,
        )
    };
    let proof = prove(provided.spec(), provided.compressed()).unwrap();
    assert!(verify(provided.spec(), provided.compressed(), &proof).is_ok());

    // Archive or circuit rejected.
    let mut corrupt = provided.compressed().to_vec();
    let middle = corrupt.len() / 2;
    corrupt[middle] ^= 0x55;
    for compressed in [&[][..], &corrupt[..corrupt.len() / 2], &corrupt] {
        assert_eq!(
            prove(provided.spec(), compressed),
            Err(MdocProverErrorCode::CircuitParsingFailure)
        );
        assert_eq!(
            verify(provided.spec(), compressed, &proof),
            Err(MdocVerifierErrorCode::CircuitParsingFailure)
        );
    }
    let mut other_hash = *provided.spec();
    other_hash.combined_hash[0] ^= 1;
    assert_eq!(
        prove(&other_hash, provided.compressed()),
        Err(MdocProverErrorCode::CircuitParsingFailure)
    );
    assert_eq!(
        verify(&other_hash, provided.compressed(), &proof),
        Err(MdocVerifierErrorCode::CircuitParsingFailure)
    );
    // A spec naming a well-formed archive whose hash circuit is compiled for
    // another attribute count: its public-input count is not the request's
    // `HASH_FIXED + HASH_PER_ATTRIBUTE * A` (DESIGN.md I3).
    let entries = |p: &provider::ProvidedCircuit| {
        CircuitArchive::from_bytes(&zstd::decode_all(p.compressed()).unwrap()).unwrap()
    };
    let own = entries(provided);
    let other = entries(test_circuits.get(req_attrs.len() % 4 + 1).unwrap());
    let (sig, hash) = (own.get("sig").unwrap(), other.get("hash").unwrap());
    let mut builder = CircuitArchiveBuilder::new();
    builder.circuit_version = Some(NEXT_VERSION as u32);
    builder.add_entry("sig", sig.circuit_id, sig.payload.clone());
    builder.add_entry("hash", hash.circuit_id, hash.payload.clone());
    let archive = builder.build();
    let mut mismatched_spec = *provided.spec();
    mismatched_spec.combined_hash = archive.combined_id;
    let mismatched = zstd::encode_all(archive.to_bytes().as_slice(), 1).unwrap();
    assert_eq!(
        prove(&mismatched_spec, &mismatched),
        Err(MdocProverErrorCode::CircuitParsingFailure)
    );
    assert_eq!(
        verify(&mismatched_spec, &mismatched, &proof),
        Err(MdocVerifierErrorCode::CircuitParsingFailure)
    );

    // Proof does not parse (verifier only).
    for bad in [&[][..], &proof[..proof.len() - 1], &proof[..4]] {
        assert_eq!(
            verify(provided.spec(), provided.compressed(), bad),
            Err(MdocVerifierErrorCode::HashParsingFailure)
        );
    }

    // Composition fails: the spec's Polygero profile cannot build it.
    let mut bad_profile = *provided.spec();
    bad_profile.polygero.k = 0;
    assert_eq!(
        prove(&bad_profile, provided.compressed()),
        Err(MdocProverErrorCode::GeneralFailure)
    );
    assert_eq!(
        verify(&bad_profile, provided.compressed(), &proof),
        Err(MdocVerifierErrorCode::GeneralFailure)
    );
    // Verification or the seal fails.
    let mut sealed = proof.clone();
    *sealed.last_mut().unwrap() ^= 1;
    assert_eq!(
        verify(provided.spec(), provided.compressed(), &sealed),
        Err(MdocVerifierErrorCode::GeneralFailure)
    );
    let mut other_now = now.as_bytes().to_vec();
    other_now[3] ^= 1;
    assert_eq!(
        run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pkx,
            &pky,
            TEST_DATA.transcript,
            &req_attrs,
            std::str::from_utf8(&other_now).unwrap(),
            doc_type,
            &proof,
        ),
        Err(MdocVerifierErrorCode::GeneralFailure)
    );
    assert_eq!(
        (
            MdocProverErrorCode::GeneralFailure as u32,
            MdocVerifierErrorCode::GeneralFailure as u32,
            MdocVerifierErrorCode::HashParsingFailure as u32
        ),
        (6, 5, 3)
    );
}

/// The combined circuit IDs of structural NEXT for one to four attributes.
/// Any change to a NEXT circuit changes them; update them in the same, reviewed commit.
const NEXT_COMBINED_IDS: [&str; 4] = [
    "0ca5ec679c803347d76b17258ca494a65d7fa2ba4cb6bca1e5e13dfab2bd5044",
    "78db26193dab7ca24624ad8b2511b0b586599e222fbb93d70378c2b1b15c1d0d",
    "bbb9930f851b29f824f894d6d9f7cc8c298e68e833588ff416ca71240b407ee0",
    "2332e04601cc4086064aa65b3c5229fc841f2aef9198cf328b550ad699fbf1fe",
];

/// Upstream's byte-offset predicate remains the single-commitment experiment's
/// parser-free archive, with its own compiler identity for each attribute count.
const PARSER_FREE_NEXT_COMBINED_IDS: [&str; 4] = [
    "73330d8479141705bfffeead55d26b923b9fc439b4516fb27648c81db1718aad",
    "b09dd5907aa327729a4a9fa3054f888290ec6a9164afaae6651e60aca6acd96f",
    "d6eef5c5c9465963d55c82919ddd1c43d5c5060d28c6a474fb95a07d7490ac66",
    "630290d5266925fdd8540b60953fbb34dc5c0408a5464d4b0569f4e196188b78",
];

#[test]
fn parser_free_next_circuit_hashes() {
    use crate::mdoc::development_provider::{
        compile_parser_free_next, tests::fixtures::one_compilation,
    };
    for (index, expected) in PARSER_FREE_NEXT_COMBINED_IDS.iter().enumerate() {
        let count = index + 1;
        let _one = one_compilation();
        let provided = compile_parser_free_next(count).unwrap();
        assert_eq!(
            hex::encode(provided.spec().combined_hash),
            *expected,
            "{count}-attribute parser-free NEXT combined circuit ID"
        );
    }
}

#[test]
fn next_circuit_hashes() {
    let test_circuits = &TestCircuits::load();
    for nattrs in 1..=4 {
        let p = test_circuits.get(nattrs).expect("circuit missing");
        assert_eq!(p.spec().version, NEXT_VERSION);
        assert_eq!(p.spec().num_attributes, nattrs);
        assert_eq!(
            hex::encode(p.spec().combined_hash),
            NEXT_COMBINED_IDS[nattrs - 1],
            "{nattrs}-attribute NEXT combined circuit ID"
        );
        let bytes = zstd::decode_all(p.compressed()).unwrap();
        let archive = CircuitArchive::from_bytes(&bytes).unwrap();
        assert_eq!(archive.combined_id, p.spec().combined_hash);
        assert!(find_zk_spec(SYSTEM_ID, &p.spec().combined_hash).is_none());
        // Validate IDs against the actual serialized term streams, not just
        // the archive header or copied registry entry.
        let p256 = crate::runtime::algebra::p256::P256Field::new();
        let gf2 = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
        let sig_entry = archive.get("sig").unwrap();
        let hash_entry = archive.get("hash").unwrap();
        let (sig, sig_tail) = CircuitReader::new(&p256)
            .from_bytes(&sig_entry.payload)
            .unwrap();
        let (hash, hash_tail) = CircuitReader::new(&gf2)
            .from_bytes(&hash_entry.payload)
            .unwrap();
        assert!(sig_tail.is_empty() && hash_tail.is_empty());
        assert_eq!(sig.id, sig_entry.circuit_id);
        assert_eq!(hash.id, hash_entry.circuit_id);
    }
}

// These counts come from the nodes the draws actually end, independently of the
// geometry summation used by the Lean metadata checker. Final sealing does
// not end a node with a draw and is deliberately excluded.
#[test]
fn next_measured_round_counts() {
    let test_circuits = &TestCircuits::load();
    let data = &TEST_DATA;
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(data);
    let coordinate = |value: &CompileNat<4>| {
        format!(
            "0x{}",
            num_bigint::BigUint::from_bytes_le(&value.to_bytes_le()).to_str_radix(16)
        )
    };
    let pkx = coordinate(&issuer_pk.0);
    let pky = coordinate(&issuer_pk.1);
    for (count, expected) in [(1, 463), (2, 468), (3, 472), (4, 475)] {
        let attrs: Vec<_> = parsed
            .attrs
            .iter()
            .cycle()
            .take(count)
            .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
            .collect();
        let provided = test_circuits.get(count).unwrap();
        let proof = run_mdoc_prover_encoded(
            provided.spec(),
            provided.compressed(),
            data.mdoc,
            &pkx,
            &pky,
            data.transcript,
            &attrs,
            now,
            "org.iso.18013.5.1.mDL",
            &mut DeterministicRng::new(42),
        )
        .unwrap();
        assert_eq!(
            proof.round_count_for_test(),
            expected,
            "{count}-attribute prover rounds"
        );
        let verified = run_mdoc_verifier(
            provided.spec(),
            provided.compressed(),
            &pkx,
            &pky,
            data.transcript,
            &attrs,
            now,
            "org.iso.18013.5.1.mDL",
            proof.as_bytes(),
        )
        .unwrap();
        assert_eq!(
            verified.round_count_for_test(),
            expected,
            "{count}-attribute verifier rounds"
        );
        check_mdoc_trace(count, provided, &proof);
        // Prover and verifier run one schedule (transcript I9).
        assert_eq!(proof.trace, verified.trace);
    }
}

/// Check one mdoc proof's trace against its wire bytes and the registry,
/// and pin the 1-attribute proof's first node: the statement and the
/// commitment.
fn check_mdoc_trace(
    count: usize,
    provided: &provider::ProvidedCircuit,
    proof: &crate::runtime::v2::transcript::EncodedProof,
) {
    use crate::runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field},
        v2::{
            proto::tests::{check_trace_matches_wire, export_vectors, node_vector},
            transcript::Transcript,
        },
    };
    let (gf2, p256) = (Gf2_128Field::new(), P256Field::new());
    let (sig, hash) = decompress_circuits(provided.compressed(), &p256, &gf2).unwrap();
    let geometry = proof_geometry(provided.spec(), &sig, &hash).unwrap();
    let bytes = proof.as_bytes();
    let mut session = Transcript::for_test(b"layout");
    let decoded =
        crate::mdoc::v2::MdocProof::read(bytes, &session.bound(&geometry.body), &gf2, &p256)
            .unwrap();
    // Every truncation and every extension fails at parse (proto I3).
    for len in 0..bytes.len() {
        let cut = crate::mdoc::v2::MdocProof::read(
            &bytes[..len],
            &session.bound(&geometry.body),
            &gf2,
            &p256,
        );
        assert!(cut.is_err(), "length {len}");
    }
    for extra in 1..=64 {
        let mut longer = bytes.to_vec();
        longer.resize(bytes.len() + extra, 0);
        let read =
            crate::mdoc::v2::MdocProof::read(&longer, &session.bound(&geometry.body), &gf2, &p256);
        assert!(read.is_err(), "{extra} extra bytes");
    }
    let polygero = &decoded.body.polygero;
    let (nonces, frontier) = polygero.authentication_bytes();
    let rows = 16 * polygero.bodies().0.rows.len() + 32 * polygero.bodies().1 .0.rows.len();
    let interactive = bytes.len() - 32 - frontier - nonces - rows;
    let trace = &proof.trace;
    check_trace_matches_wire(trace, bytes, 4, interactive);
    // The statement: identity, three circuits, two layouts, the adapter, the
    // joint geometry and two public input vectors; then the commitment.
    let tags: Vec<u64> = trace.messages().take(11).map(|m| m.tag).collect();
    assert_eq!(tags, [16, 18, 18, 18, 19, 19, 22, 20, 21, 21, 32]);
    // Check the setup payload against the actual compiler output. Glorious
    // includes the structural parser in this hash circuit, so its IDs and
    // committed witness differ from upstream's parser-free mdoc vector.
    let identity = trace.messages().next().unwrap();
    let mut identity_spec = provided.spec().combined_hash.to_vec();
    identity_spec.extend((provided.spec().version as u64).to_le_bytes());
    identity_spec.extend((count as u64).to_le_bytes());
    assert_eq!(
        &identity.payload[identity.payload.len() - 48..],
        &identity_spec
    );
    assert_eq!(trace.messages().nth(1).unwrap().payload, hash.id);
    assert_eq!(trace.messages().nth(3).unwrap().payload, sig.id);

    // These are exactly the message schemas of the two-field mdoc protocol.
    // Other protocols have their own identities, layouts and responses.
    use crate::runtime::v2::proto::tags::Tag;
    let seen: std::collections::BTreeSet<u64> = trace.messages().map(|m| m.tag).collect();
    let expected: std::collections::BTreeSet<u64> = [
        Tag::MdocStatement,
        Tag::Circuit,
        Tag::CommitmentLayout,
        Tag::JointGeometry,
        Tag::PublicInputs,
        Tag::AdapterLayout,
        Tag::Commitment,
        Tag::FingerprintResponse,
        Tag::SumcheckRound,
        Tag::SumcheckCross,
        Tag::SumcheckClaims,
        Tag::SplitOpening,
        Tag::P256AdapterQuotients,
        Tag::PackingU,
        Tag::PackingA,
        Tag::PolygeroResponse,
        Tag::Seal,
    ]
    .into_iter()
    .map(Tag::value)
    .collect();
    assert_eq!(seen, expected);
    let public: Vec<_> = trace
        .messages()
        .skip(8)
        .take(2)
        .map(|m| m.schema[0].1)
        .collect();
    let counts = [
        public::HASH_FIXED + public::HASH_PER_ATTRIBUTE * count,
        public::SIGNATURE,
    ];
    assert_eq!(public, counts.map(|x| x as u64));
    // The absorbed geometry is the parsing geometry (transcript I2, I3):
    // the one profile is in `JointGeometry`, and it is the spec's.
    let joint = trace.messages().nth(7).unwrap();
    let nats: Vec<u64> = joint
        .payload
        .as_chunks::<8>()
        .0
        .iter()
        .map(|x| u64::from_le_bytes(*x))
        .collect();
    let c = geometry.body.config();
    assert_eq!(nats, [c.k as u64, c.s as u64, c.n as u64, c.t as u64]);
    assert_eq!(provided.spec().polygero, c);
    if count == 1 {
        let node = &trace.nodes[0];
        export_vectors(&format!(
            "## 1-attribute mdoc proof (TEST_DATA, first attribute, DeterministicRng(42)): \
             first node, the statement and the Commitment\n\n{}",
            node_vector("mdoc 1 attribute", 0, node)
        ));
        assert_eq!(
            hex::encode(<sha2::Sha256 as sha2::Digest>::digest(node)),
            "e0847e143bede6d4795976e6fde0c2ecd468f4f7a55b1a7caf84646c0d8339f6"
        );
    }
}

/// A false statement fails before the prover draws a coin, with the circuit's
/// `GeneralFailure`: another issuer key, another session transcript (whose
/// device signature fails), and the negative vectors (mdoc DESIGN.md I10).
#[test]
fn false_statements_fail_before_sampling() {
    let test_circuits = &TestCircuits::load();
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let req_attrs = requested_fixture_attributes(&parsed, "TEST_DATA");
    let provided = test_circuits.get(req_attrs.len()).unwrap();
    let (gx, gy) = (
        "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
    );
    let other_session = b"\x66inputs";
    for (pkx, pky, transcript) in [
        (gx, gy, TEST_DATA.transcript),
        (TEST_DATA.pkx, TEST_DATA.pky, &other_session[..]),
    ] {
        let mut rng = DeterministicRng::new(42);
        assert_eq!(
            run_mdoc_prover_inner(
                provided.spec(),
                provided.compressed(),
                TEST_DATA.mdoc,
                pkx,
                pky,
                transcript,
                &req_attrs,
                now,
                TEST_DATA.doc_type,
                &mut rng,
            ),
            Err(MdocProverErrorCode::GeneralFailure)
        );
        assert_eq!(rng.state, 42, "a false statement must fail before sampling");
    }
}

/// A document longer than the v2 cap fails as an undecodable MSO (mdoc
/// DESIGN.md, "Size limits").
#[test]
fn oversized_document_is_a_decoding_failure() {
    let test_circuits = &TestCircuits::load();
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let req_attrs = requested_fixture_attributes(&parsed, "TEST_DATA");
    let provided = test_circuits.get(req_attrs.len()).unwrap();
    let mut mdoc = TEST_DATA.mdoc.to_vec();
    mdoc.resize(256 * 1024 + 1, 0);
    assert_eq!(
        run_mdoc_prover_inner(
            provided.spec(),
            provided.compressed(),
            &mdoc,
            TEST_DATA.pkx,
            TEST_DATA.pky,
            TEST_DATA.transcript,
            &req_attrs,
            now,
            TEST_DATA.doc_type,
            &mut DeterministicRng::new(42),
        ),
        Err(MdocProverErrorCode::MsoDecodingFailure)
    );
}

/// Check the shared development profile and its compiled circuit geometry.
#[test]
fn next_v2_parameters() {
    for (_, provided) in TestCircuits::load().circuits {
        assert_v2_parameters(provided.spec(), provided.compressed());
    }
}

fn assert_v2_parameters(spec: &ZkSpecStruct, compressed: &[u8]) {
    use crate::{
        mdoc::v2::domains::with_domains,
        runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
    };
    let f = Gf2_128Field::new();
    let p = P256Field::new();
    let (sig, hash) = decompress_circuits(compressed, &p, &f).unwrap();
    let expected = PolygeroConfig {
        k: 349,
        s: 12,
        n: 2443,
        t: 84,
    };
    assert_eq!(spec.polygero, expected);
    with_domains(&f, &p, |domains| {
        // The hash circuit is archived at its natural width: the link mask,
        // pads and tree leaves lie beyond it, so it cannot address them.
        let link = link_for_test(spec, &sig, &hash, domains).unwrap();
        assert_eq!(link.0, hash.raw.ninput);
        assert!(link.1 > link.0);
        assert!(expected.can_interpolate(domains.0));
        assert!(expected.can_interpolate(domains.1));
    });
    let geometry = proof_geometry(spec, &sig, &hash).unwrap();
    // Keep the numerical frontend and Merkle charges tied to the actual
    // hash-plus-adapter geometry, including entries for both quad fragments.
    let binary = geometry.body.host().sumcheck();
    let native = geometry.body.split().sumcheck();
    // Pin the structural frontend's compiled schedules and protocol charges;
    // the parser-free frontend has fewer binary witnesses and rounds.
    let variant = spec.num_attributes.checked_sub(1).unwrap();
    let binary_rounds = binary.layers().iter().sum::<usize>();
    let native_rounds = native.layers().iter().sum::<usize>();
    assert_eq!(binary_rounds, [278, 283, 287, 290][variant]);
    assert_eq!(binary.layers().len(), 19);
    assert_eq!(native_rounds, 118);
    assert_eq!(native.layers().len(), 11);
    let binary_charge = 2 * binary_rounds + 2 * binary.layers().len() + 2;
    let native_charge = 2 * native_rounds + 2 * native.layers().len();
    assert_eq!(binary_charge, [596, 606, 614, 620][variant]);
    assert_eq!(native_charge, 258);
    let rounds =
        binary_rounds + native_rounds + 2 * (binary.layers().len() + native.layers().len()) + 7;
    assert_eq!(rounds, [463, 468, 472, 475][variant]);
    assert!(rounds <= 475);
    assert!(
        binary.layers().iter().sum::<usize>()
            + native.layers().iter().sum::<usize>()
            + 4 * (binary.layers().len() + native.layers().len())
            + 16
            <= 1204
    );
}
