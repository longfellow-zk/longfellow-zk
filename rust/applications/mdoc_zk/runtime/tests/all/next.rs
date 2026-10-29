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
    core::algebra::Nat,
    mdoc::{
        circuits::parse_test_data,
        v2::{
            provider, req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner, RequestedAttribute,
        },
    },
};

struct TestCircuits {
    circuits: std::collections::HashMap<usize, provider::ProvidedCircuit>,
}

impl TestCircuits {
    fn compile_all() -> Self {
        let compile = |count| {
            use crate::mdoc::development_provider::{materialize, CircuitRequest, ProvidedCircuit};
            let ProvidedCircuit::V2(provided) = materialize(CircuitRequest::Next {
                num_attributes: count,
            })
            .unwrap() else {
                panic!("NEXT must use v2")
            };
            assert_v2_parameters(provided.spec(), provided.compressed());
            (count, provided)
        };
        // Concurrent compiler allocations exceed the 32-bit address space.
        #[cfg(target_pointer_width = "32")]
        let circuits = (1..=4).map(compile).collect();
        #[cfg(not(target_pointer_width = "32"))]
        let circuits = std::thread::scope(|scope| {
            let tasks: Vec<_> = (1..=4)
                .map(|count| scope.spawn(move || compile(count)))
                .collect();
            tasks.into_iter().map(|task| task.join().unwrap()).collect()
        });
        Self { circuits }
    }

    fn get(&self, nattrs: usize) -> Option<&provider::ProvidedCircuit> {
        self.circuits.get(&nattrs)
    }
}

fn run_next_mdoc_flow(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = crate::mdoc::testcases::vectors::TEST_DATA.mdoc;
    let transcript = crate::mdoc::testcases::vectors::TEST_DATA.transcript;
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

    let mut rng = crate::runtime::random::DeterministicRng::new(42);
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

    assert_eq!(&zkproof[96..100], b"LFV4");
    assert_eq!(
        crate::mdoc::v2::SYSTEM_ID,
        crate::mdoc::runtime::LONGFELLOW_V2
    );

    let verify_res = run_mdoc_verifier_inner(
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

fn run_next_mdoc_subset_flow(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .step_by(2)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = crate::mdoc::testcases::vectors::TEST_DATA.mdoc;
    let transcript = crate::mdoc::testcases::vectors::TEST_DATA.transcript;
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

    let mut rng = crate::runtime::random::DeterministicRng::new(42);
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

    let verify_res = run_mdoc_verifier_inner(
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

fn run_next_mdoc_all_positive_cases(test_circuits: &TestCircuits) {
    for case in crate::mdoc::testcases::vectors::ALL_TEST_CASES {
        if case.name.starts_with("fail-") {
            continue;
        }
        let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(case.data);
        let nattrs = parsed.attrs.len();
        if nattrs == 0 || nattrs > 4 {
            continue;
        }
        let ns = if case.data.doc_type.starts_with("org.iso.18013.5.1") {
            "org.iso.18013.5.1"
        } else {
            case.data.doc_type
        };
        let req_attrs: Vec<RequestedAttribute> = parsed
            .attrs
            .iter()
            .take(nattrs)
            .map(|a| req_attr(ns, &a.name, &a.cbor_value))
            .collect();

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

        let mut rng = crate::runtime::random::DeterministicRng::new(42);

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

        let verify_res = run_mdoc_verifier_inner(
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

fn run_next_mdoc_all_negative_cases(test_circuits: &TestCircuits) {
    let mut executed = 0;
    let mut skipped_for_attribute_count = Vec::new();
    for case in crate::mdoc::testcases::vectors::ALL_TEST_CASES {
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
        let ns = if case.data.doc_type.starts_with("org.iso.18013.5.1") {
            "org.iso.18013.5.1"
        } else {
            case.data.doc_type
        };
        let mut req_attrs: Vec<RequestedAttribute> = parsed
            .attrs
            .iter()
            .take(nattrs)
            .map(|a| req_attr(ns, &a.name, &a.cbor_value))
            .collect();

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

        let mut rng = crate::runtime::random::DeterministicRng::new(42);

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
            Err(crate::mdoc::v2::MdocProverErrorCode::GeneralFailure),
            "wrong prover failure for negative case: {}",
            case.name
        );
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

fn run_next_verifier_negative_cases(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = crate::mdoc::testcases::vectors::TEST_DATA.mdoc;
    let transcript = crate::mdoc::testcases::vectors::TEST_DATA.transcript;
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
    let mut rng = crate::runtime::random::DeterministicRng::new(42);
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
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong PKX"
    );

    // 2. Wrong PKY
    let invalid_key_y_formatted =
        "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef";
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong PKY"
    );

    // 3. Wrong Transcript
    let mut bad_transcript = transcript.to_vec();
    if bad_transcript.is_empty() {
        bad_transcript.push(0xff);
    } else {
        bad_transcript[0] ^= 0xff;
    }
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong transcript"
    );

    // 4. Wrong Timestamp
    let bad_now = "2099-01-01T00:00:00Z";
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong timestamp"
    );

    // 5. Wrong Doc Type
    let bad_doc_type = "org.iso.18013.5.1.fake";
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong doc_type"
    );

    // 6. Empty Doc Type
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject empty doc_type"
    );

    // 7. Attribute Mismatch - Wrong Value
    let mut bad_attrs_val = req_attrs.clone();
    bad_attrs_val[0].cbor_value = vec![0x63, b'f', b'o', b'o']; // Text "foo"
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong attribute value"
    );

    // 8. Attribute Mismatch - Wrong ID
    let mut bad_attrs_id = req_attrs.clone();
    bad_attrs_id[0].id = vec![b'x'];
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong attribute id"
    );

    // 9. Attribute Number Mismatch - Too Few
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject empty attributes slice"
    );

    // 10. Attribute Number Mismatch - Too Many
    let mut two_attrs = req_attrs.clone();
    two_attrs.push(req_attrs[0].clone());
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject too many attributes"
    );

    // 11. Unsupported ZkSpec Version (version 0 and version 99)
    let mut bad_spec_0 = *provided.spec();
    bad_spec_0.version = 0;
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::InvalidZkSpecVersion),
        "Verifier should reject version 0"
    );

    let mut bad_spec_99 = *provided.spec();
    bad_spec_99.version = 99;
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::InvalidZkSpecVersion),
        "Verifier should reject version 99"
    );
}

fn run_next_verifier_attribute_reordering_and_duplicates(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
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

    let mdoc_bytes = crate::mdoc::testcases::vectors::TEST_DATA.mdoc;
    let transcript = crate::mdoc::testcases::vectors::TEST_DATA.transcript;
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
    let mut rng = crate::runtime::random::DeterministicRng::new(42);
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
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject reordered attributes"
    );

    let duplicates = vec![two_attrs[0].clone(), two_attrs[0].clone()];
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject duplicate attributes"
    );
}

fn run_next_verifier_bad_proofs(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = crate::mdoc::testcases::vectors::TEST_DATA.mdoc;
    let transcript = crate::mdoc::testcases::vectors::TEST_DATA.transcript;
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
    let mut rng = crate::runtime::random::DeterministicRng::new(42);
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
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::HashParsingFailure),
        "Verifier should reject empty proof"
    );

    // 2. Random bytes of various lengths
    for len in [10, 100, 1000, 5000, 10000, 20000] {
        let random_bytes: Vec<u8> = (0..len)
            .map(|i| u8::try_from(i * 37 % 256).unwrap())
            .collect();
        assert_eq!(
            run_mdoc_verifier_inner(
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
            Err(crate::mdoc::v2::MdocVerifierErrorCode::HashParsingFailure),
            "Verifier should reject random proof of len {len}"
        );
    }

    // 3. Bit/byte flips in valid proof
    for idx in [10, 100, zkproof.len() / 2, zkproof.len().saturating_sub(10)] {
        if idx < zkproof.len() {
            let mut flipped = zkproof.clone();
            flipped[idx] ^= 0x55;
            assert_eq!(
                run_mdoc_verifier_inner(
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
                Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
                "Verifier should reject proof with byte flip at index {idx}"
            );
        }
    }

    // 4. Truncated proof
    if zkproof.len() > 100 {
        let truncated = &zkproof[..zkproof.len() - 100];
        assert_eq!(
            run_mdoc_verifier_inner(
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
            Err(crate::mdoc::v2::MdocVerifierErrorCode::HashParsingFailure),
            "Verifier should reject truncated proof"
        );
    }

    // 5. Extended proof with trailing garbage
    let mut extended = zkproof.clone();
    extended.extend_from_slice(&[0xaa; 100]);
    assert_eq!(
        run_mdoc_verifier_inner(
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
        Err(crate::mdoc::v2::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject proof with trailing garbage"
    );
}

fn run_circuit_supports_cbor() {
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

fn run_namespace_mixup(test_circuits: &TestCircuits) {
    use crate::mdoc::v2::{req_attr, same_namespace};

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

    let (issuer_pk, _, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
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

    let res = run_mdoc_verifier_inner(
        provided.spec(),
        provided.compressed(),
        &pubkey_x_string,
        &pubkey_y_formatted,
        crate::mdoc::testcases::vectors::TEST_DATA.transcript,
        &mixed_attrs,
        now,
        "org.iso.18013.5.1.mDL",
        &[0u8; 1000],
    );
    assert_eq!(
        res,
        Err(crate::mdoc::v2::MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject mixed namespace"
    );
}

fn run_next_circuit_hashes(test_circuits: &TestCircuits) {
    for nattrs in 1..=4 {
        let p = test_circuits.get(nattrs).expect("circuit missing");
        assert_eq!(p.spec().version, crate::mdoc::circuits::NEXT_VERSION);
        assert_eq!(p.spec().num_attributes, nattrs);
        let bytes = zstd::decode_all(p.compressed()).unwrap();
        let archive = crate::core::proto::archive::CircuitArchive::from_bytes(&bytes).unwrap();
        assert_eq!(archive.combined_id, p.spec().combined_hash);
        assert!(
            crate::mdoc::v2::find_zk_spec(crate::mdoc::v2::SYSTEM_ID, &p.spec().combined_hash)
                .is_none()
        );
        // Validate IDs against the actual serialized term streams, not just
        // the archive header or copied registry entry.
        let p256 = crate::runtime::algebra::p256::P256Field::new();
        let gf2 = crate::runtime::algebra::gf2_128::Gf2_128Field::new();
        let sig_entry = archive.get("sig").unwrap();
        let hash_entry = archive.get("hash").unwrap();
        let (sig, sig_tail) = crate::core::proto::reader::CircuitReader::new(
            &p256,
            crate::core::proto::FieldID::P256,
        )
        .from_bytes_lfc3(&sig_entry.payload, true)
        .unwrap();
        let (hash, hash_tail) = crate::core::proto::reader::CircuitReader::new(
            &gf2,
            crate::core::proto::FieldID::Gf2_128,
        )
        .from_bytes_lfc3(&hash_entry.payload, true)
        .unwrap();
        assert!(sig_tail.is_empty() && hash_tail.is_empty());
        assert_eq!(sig.id, sig_entry.circuit_id);
        assert_eq!(hash.id, hash_entry.circuit_id);
    }
}

#[test]
fn test_all_next_zk() {
    let test_circuits = TestCircuits::compile_all();
    run_next_circuit_hashes(&test_circuits);
    run_next_mdoc_flow(&test_circuits);
    run_next_mdoc_subset_flow(&test_circuits);
    run_next_mdoc_all_positive_cases(&test_circuits);
    run_next_mdoc_all_negative_cases(&test_circuits);
    run_next_verifier_negative_cases(&test_circuits);
    run_next_verifier_attribute_reordering_and_duplicates(&test_circuits);
    run_next_verifier_bad_proofs(&test_circuits);
    run_circuit_supports_cbor();
    run_namespace_mixup(&test_circuits);
}

/// Check the development parameters against the rate-1/7 selector.
fn assert_v2_parameters(spec: &crate::mdoc::v2::ZkSpecStruct, compressed: &[u8]) {
    use crate::runtime::algebra::{
        fp2::Fp2Field,
        gf2_128::Gf2_128Field,
        p256::{P256Field, P256Subfield},
        range_interpolation::{
            BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
        },
        subfield_v1::BinarySubfield,
        SupportsFFT,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let d = BinaryInterpolatorFactory::new(&f, &sf);
    let p = P256Field::new();
    let extension = Fp2Field::new(&p);
    let pd = QuadraticExtensionFftInterpolatorFactory::new(
        &p,
        &extension,
        extension.omega(),
        extension.omega_order(),
    );
    let psf = P256Subfield::new(&p);
    let (sig, hash) = crate::mdoc::v2::decompress_circuits(compressed, &p, &f, false).unwrap();
    let expected_hash = expected_parameters(&hash, &d, &f, &sf);
    let expected_sig = expected_parameters(&sig, &pd, &p, &psf);
    assert_eq!(
        Some(spec.configs()),
        Some((expected_hash, expected_sig)),
        "NEXT parameters for {} attributes",
        spec.num_attributes
    );
}

fn expected_parameters<
    const W: usize,
    F: crate::runtime::algebra::RuntimeField<W>
        + crate::core::algebra::SerializableField
        + crate::runtime::algebra::PackingField,
    D: crate::runtime::algebra::RangeInterpolatorFactory<W, F>,
    SF: crate::runtime::algebra::SubfieldV1<E = F::E>,
>(
    circuit: &crate::core::proto::v2::Circuit<F>,
    domain: &D,
    f: &F,
    _sf: &SF,
) -> crate::runtime::proto::polygero::PolygeroConfig {
    let (layout, _, products) = crate::runtime::proto::zk_v2::packing_layout(circuit, f).unwrap();
    let nw = layout.witness_count;
    crate::compile::polygero::tune_large_field_at_rate(
        7,
        nw,
        &products,
        f.serialized_size_bytes(),
        |config| config.can_interpolate(domain),
    )
    .unwrap()
}
