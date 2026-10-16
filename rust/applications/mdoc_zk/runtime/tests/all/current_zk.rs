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

use compile_algebra::CompileNat;
use core_algebra::Nat;
use mdoc_zk_circuits::parse_test_data;
use mdoc_zk_runtime::{
    provider, req_attr, req_attr_ge, req_attr_le, req_pnym, run_mdoc_prover_inner,
    run_mdoc_prover_inner_ext, run_mdoc_verifier_inner, RequestedAttribute,
};

struct TestCircuits {
    circuits: std::collections::HashMap<(usize, bool), provider::ProvidedCircuit>,
}

impl TestCircuits {
    fn compile_all() -> Self {
        let first_spec = &mdoc_zk_runtime::CURRENT_ZK_SPECS[0];
        let hash_profile = mdoc_zk_compile::LigeroProfile {
            rateinv: first_spec.ligero_hash.rateinv,
            nreq: first_spec.ligero_hash.nreq,
        };
        let sig_profile = mdoc_zk_compile::LigeroProfile {
            rateinv: first_spec.ligero_sig.rateinv,
            nreq: first_spec.ligero_sig.nreq,
        };
        let results = mdoc_zk_compile::compile_all_circuits(hash_profile, sig_profile);
        let p256 = runtime_algebra::p256::P256Field::new();
        let gf2 = runtime_algebra::gf2_128::Gf2_128Field::new();
        let mut circuits = std::collections::HashMap::new();
        let mut mismatches = Vec::new();
        for (key, res) in results {
            let (lfa_bytes, config_sig, config_hash) =
                res.unwrap_or_else(|e| panic!("Failed to compile circuit {key:?}: {e}"));
            let spec = mdoc_zk_runtime::CURRENT_ZK_SPECS
                .iter()
                .find(|s| (s.num_attributes, s.pnym) == key)
                .unwrap_or_else(|| panic!("no CURRENT_ZK_SPECS entry for circuit {key:?}"));
            let compressed =
                zstd::encode_all(&lfa_bytes[..], mdoc_zk_circuits::config::K_ZSTD_LEVEL).unwrap();
            let (c_sig, c_hash) =
                mdoc_zk_runtime::decompress_circuits(&compressed, &p256, &gf2).unwrap();
            let mut hasher = <sha2::Sha256 as sha2::Digest>::new();
            sha2::Digest::update(&mut hasher, c_sig.id);
            sha2::Digest::update(&mut hasher, c_hash.id);
            let combined_hash: [u8; 32] = sha2::Digest::finalize(hasher).into();
            println!(
                "v8 circuit {key:?}: hash_block_enc={}, sig_block_enc={}, combined_hash={:?}",
                config_hash.block_enc, config_sig.block_enc, combined_hash
            );
            if config_hash != spec.ligero_hash
                || config_sig != spec.ligero_sig
                || combined_hash != spec.combined_hash
            {
                mismatches.push(key);
            }
            let archive = core_proto::archive::CircuitArchive::from_bytes(&lfa_bytes).unwrap();
            let previous = circuits.insert(
                key,
                provider::ProvidedCircuit {
                    name: spec.combined_hash_hex(),
                    spec: *spec,
                    archive,
                    compressed,
                },
            );
            assert!(previous.is_none(), "circuit {key:?} compiled twice");
        }
        assert!(
            mismatches.is_empty(),
            "Spec mismatches for circuits: {mismatches:?}"
        );
        assert_eq!(
            circuits.len(),
            mdoc_zk_runtime::CURRENT_ZK_SPECS.len(),
            "every CURRENT_ZK_SPECS entry must have been compiled"
        );
        Self { circuits }
    }

    fn get(&self, nattrs: usize) -> Option<&provider::ProvidedCircuit> {
        let key = match nattrs {
            1 => (1, false),
            2..=4 => (4, false),
            _ => return None,
        };
        self.circuits.get(&key)
    }

    fn get_pnym(&self) -> Option<&provider::ProvidedCircuit> {
        self.circuits.get(&(0, true))
    }
}

fn run_current_mdoc_flow(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = mdoc_zk_testcases::vectors::TEST_DATA.mdoc;
    let transcript = mdoc_zk_testcases::vectors::TEST_DATA.transcript;
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

    let mut rng = runtime_random::DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        &provided.spec,
        &provided.compressed,
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
        &provided.spec,
        &provided.compressed,
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

fn run_current_mdoc_subset_flow(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .step_by(2)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = mdoc_zk_testcases::vectors::TEST_DATA.mdoc;
    let transcript = mdoc_zk_testcases::vectors::TEST_DATA.transcript;
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

    let mut rng = runtime_random::DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        &provided.spec,
        &provided.compressed,
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
        &provided.spec,
        &provided.compressed,
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

fn run_current_mdoc_all_positive_cases(test_circuits: &TestCircuits) {
    for case in mdoc_zk_testcases::vectors::ALL_TEST_CASES {
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

        if !mdoc_zk_runtime::same_namespace(&req_attrs) {
            continue;
        }
        if req_attrs
            .iter()
            .any(|a| !mdoc_zk_runtime::circuit_supports(&a.cbor_value))
        {
            continue;
        }

        let Some(provided) = test_circuits.get(nattrs) else {
            continue;
        };

        let mut rng = runtime_random::DeterministicRng::new(42);

        let zkproof = run_mdoc_prover_inner(
            &provided.spec,
            &provided.compressed,
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
            &provided.spec,
            &provided.compressed,
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

fn run_current_mdoc_all_negative_cases(test_circuits: &TestCircuits) {
    let mut executed = 0;
    let mut skipped_for_attribute_count = Vec::new();
    for case in mdoc_zk_testcases::vectors::ALL_TEST_CASES {
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

        let mut rng = runtime_random::DeterministicRng::new(42);

        let zkproof_res = run_mdoc_prover_inner(
            &provided.spec,
            &provided.compressed,
            case.data.mdoc,
            case.data.pkx,
            case.data.pky,
            case.data.transcript,
            &req_attrs,
            now,
            case.data.doc_type,
            &mut rng,
        );
        // Every executable negative vector is an `Eq` mismatch (`age_over_18` requested as
        // `false` against a document stating `true`). The prover evaluates the predicate on
        // the host before proving, so this is a fast, well-typed rejection; the in-circuit
        // rejection of a wrong public value is covered by the verifier-side tests below.
        assert_eq!(
            zkproof_res,
            Err(mdoc_zk_runtime::MdocProverErrorCode::PredicateNotSatisfied),
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

fn run_current_verifier_negative_cases(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = mdoc_zk_testcases::vectors::TEST_DATA.mdoc;
    let transcript = mdoc_zk_testcases::vectors::TEST_DATA.transcript;
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
    let mut rng = runtime_random::DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        &provided.spec,
        &provided.compressed,
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
            &provided.spec,
            &provided.compressed,
            invalid_key_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong PKX"
    );

    // 2. Wrong PKY
    let invalid_key_y_formatted =
        "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef";
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            invalid_key_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
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
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            &bad_transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong transcript"
    );

    // 4. Wrong Timestamp
    let bad_now = "2099-01-01T00:00:00Z";
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            bad_now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong timestamp"
    );

    // 5. Wrong Doc Type
    let bad_doc_type = "org.iso.18013.5.1.fake";
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            bad_doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong doc_type"
    );

    // 6. Empty Doc Type
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            "",
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject empty doc_type"
    );

    // 7. Attribute Mismatch - Wrong Value
    let mut bad_attrs_val = req_attrs.clone();
    bad_attrs_val[0].cbor_value = vec![0x63, b'f', b'o', b'o']; // Text "foo"
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &bad_attrs_val,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong attribute value"
    );

    // 8. Attribute Mismatch - Wrong ID
    let mut bad_attrs_id = req_attrs.clone();
    bad_attrs_id[0].id = vec![b'x'];
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &bad_attrs_id,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject wrong attribute id"
    );

    // 9. Attribute Number Mismatch - Too Few
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &[],
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject empty attributes slice"
    );

    // 10. Attribute Number Mismatch - Too Many
    let mut too_many_attrs = req_attrs.clone();
    while too_many_attrs.len() <= provided.spec.num_attributes {
        too_many_attrs.push(req_attrs[0].clone());
    }
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &too_many_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject too many attributes"
    );

    // 11. Unsupported ZkSpec Version (version 0 and version 99)
    let mut bad_spec_0 = provided.spec;
    bad_spec_0.version = 0;
    assert_eq!(
        run_mdoc_verifier_inner(
            &bad_spec_0,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::InvalidZkSpecVersion),
        "Verifier should reject version 0"
    );

    let mut bad_spec_99 = provided.spec;
    bad_spec_99.version = 99;
    assert_eq!(
        run_mdoc_verifier_inner(
            &bad_spec_99,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::InvalidZkSpecVersion),
        "Verifier should reject version 99"
    );
}

fn run_current_verifier_attribute_reordering_and_duplicates(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
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

    let mdoc_bytes = mdoc_zk_testcases::vectors::TEST_DATA.mdoc;
    let transcript = mdoc_zk_testcases::vectors::TEST_DATA.transcript;
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
    let mut rng = runtime_random::DeterministicRng::new(42);
    let zkproof_res = run_mdoc_prover_inner(
        &provided.spec,
        &provided.compressed,
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
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &reordered,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject reordered attributes"
    );

    let duplicates = vec![two_attrs[0].clone(), two_attrs[0].clone()];
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &duplicates,
            now,
            doc_type,
            &zkproof
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject duplicate attributes"
    );
}

fn run_current_verifier_bad_proofs(test_circuits: &TestCircuits) {
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = mdoc_zk_testcases::vectors::TEST_DATA.mdoc;
    let transcript = mdoc_zk_testcases::vectors::TEST_DATA.transcript;
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
    let mut rng = runtime_random::DeterministicRng::new(42);
    let zkproof = run_mdoc_prover_inner(
        &provided.spec,
        &provided.compressed,
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
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &[]
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::HashParsingFailure),
        "Verifier should reject empty proof"
    );

    // 2. Random bytes of various lengths
    for len in [10, 100, 1000, 5000, 10000, 20000] {
        let random_bytes: Vec<u8> = (0..len)
            .map(|i| u8::try_from(i * 37 % 256).unwrap())
            .collect();
        assert_eq!(
            run_mdoc_verifier_inner(
                &provided.spec,
                &provided.compressed,
                &pubkey_x_string,
                &pubkey_y_formatted,
                transcript,
                &req_attrs,
                now,
                doc_type,
                &random_bytes
            ),
            Err(mdoc_zk_runtime::MdocVerifierErrorCode::HashParsingFailure),
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
                    &provided.spec,
                    &provided.compressed,
                    &pubkey_x_string,
                    &pubkey_y_formatted,
                    transcript,
                    &req_attrs,
                    now,
                    doc_type,
                    &flipped
                ),
                Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
                "Verifier should reject proof with byte flip at index {idx}"
            );
        }
    }

    // 4. Truncated proof
    if zkproof.len() > 100 {
        let truncated = &zkproof[..zkproof.len() - 100];
        assert_eq!(
            run_mdoc_verifier_inner(
                &provided.spec,
                &provided.compressed,
                &pubkey_x_string,
                &pubkey_y_formatted,
                transcript,
                &req_attrs,
                now,
                doc_type,
                truncated
            ),
            Err(mdoc_zk_runtime::MdocVerifierErrorCode::HashParsingFailure),
            "Verifier should reject truncated proof"
        );
    }

    // 5. Extended proof with trailing garbage
    let mut extended = zkproof.clone();
    extended.extend_from_slice(&[0xaa; 100]);
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided.spec,
            &provided.compressed,
            &pubkey_x_string,
            &pubkey_y_formatted,
            transcript,
            &req_attrs,
            now,
            doc_type,
            &extended
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier should reject proof with trailing garbage"
    );
}

fn run_circuit_supports_cbor() {
    use mdoc_zk_runtime::circuit_supports;

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
    use mdoc_zk_runtime::{req_attr, same_namespace};

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
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
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
        &provided.spec,
        &provided.compressed,
        &pubkey_x_string,
        &pubkey_y_formatted,
        mdoc_zk_testcases::vectors::TEST_DATA.transcript,
        &mixed_attrs,
        now,
        "org.iso.18013.5.1.mDL",
        &[0u8; 1000],
    );
    assert_eq!(
        res,
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::AttributeNumberMismatch),
        "Verifier should reject mixed namespace"
    );
}

fn run_current_circuit_hashes(test_circuits: &TestCircuits) {
    assert_eq!(
        test_circuits.get(1).expect("circuit missing").spec,
        mdoc_zk_runtime::CURRENT_ZK_SPECS[0]
    );
    for nattrs in 2..=4 {
        assert_eq!(
            test_circuits.get(nattrs).expect("circuit missing").spec,
            mdoc_zk_runtime::CURRENT_ZK_SPECS[1]
        );
    }
    assert_eq!(
        test_circuits.get_pnym().expect("pnym circuit missing").spec,
        mdoc_zk_runtime::CURRENT_ZK_SPECS[2]
    );
}

fn run_current_date_comparison_tests(test_circuits: &TestCircuits) {
    let test_data = &mdoc_zk_testcases::vectors::BIRTHDATE_1971_09_01_MDOC_3;
    let mdoc_bytes = test_data.mdoc;
    let transcript = test_data.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";
    let now = test_data.now;
    let pkx = test_data.pkx;
    let pky = test_data.pky;

    // Document has birth_date = 1971-09-01 (tag 1004 full-date)
    let provided_1 = test_circuits.get(1).unwrap();
    let provided_4 = test_circuits.get(2).unwrap();

    // 1. Positive Le comparison: birth_date <= 2000-01-01
    let le_2000 = [req_attr_le(
        "org.iso.18013.5.1",
        "birth_date",
        *b"\xd9\x03\xec\x6a2000-01-01",
    )];
    let mut rng = runtime_random::DeterministicRng::new(42);
    let proof_le = run_mdoc_prover_inner(
        &provided_1.spec,
        &provided_1.compressed,
        mdoc_bytes,
        pkx,
        pky,
        transcript,
        &le_2000,
        now,
        doc_type,
        &mut rng,
    )
    .expect("Le 2000-01-01 proof should succeed");
    run_mdoc_verifier_inner(
        &provided_1.spec,
        &provided_1.compressed,
        pkx,
        pky,
        transcript,
        &le_2000,
        now,
        doc_type,
        &proof_le,
    )
    .expect("Le 2000-01-01 verification should succeed");

    // Verifier must reject if op is changed to Eq or Ge
    let eq_2000 = [req_attr(
        "org.iso.18013.5.1",
        "birth_date",
        *b"\xd9\x03\xec\x6a2000-01-01",
    )];
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_1.spec,
            &provided_1.compressed,
            pkx,
            pky,
            transcript,
            &eq_2000,
            now,
            doc_type,
            &proof_le,
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure),
        "Verifier must reject Le proof when verified with Eq"
    );

    // 2. Positive boundary Le and Ge: birth_date <= 1971-09-01 and birth_date >= 1971-09-01
    // combined in a 2-attribute request (exercising 4-attr circuit duplicate padding)
    let range_exact = [
        req_attr_ge(
            "org.iso.18013.5.1",
            "birth_date",
            *b"\xd9\x03\xec\x6a1971-09-01",
        ),
        req_attr_le(
            "org.iso.18013.5.1",
            "birth_date",
            *b"\xd9\x03\xec\x6a1971-09-01",
        ),
    ];
    let mut rng = runtime_random::DeterministicRng::new(43);
    let proof_range = run_mdoc_prover_inner(
        &provided_4.spec,
        &provided_4.compressed,
        mdoc_bytes,
        pkx,
        pky,
        transcript,
        &range_exact,
        now,
        doc_type,
        &mut rng,
    )
    .expect("Range proof should succeed");
    run_mdoc_verifier_inner(
        &provided_4.spec,
        &provided_4.compressed,
        pkx,
        pky,
        transcript,
        &range_exact,
        now,
        doc_type,
        &proof_range,
    )
    .expect("Range verification should succeed");

    // 3. Negative Le: birth_date <= 1970-01-01 (false since 1971-09-01 > 1970-01-01)
    let le_1970 = [req_attr_le(
        "org.iso.18013.5.1",
        "birth_date",
        *b"\xd9\x03\xec\x6a1970-01-01",
    )];
    let mut rng = runtime_random::DeterministicRng::new(44);
    assert_eq!(
        run_mdoc_prover_inner(
            &provided_1.spec,
            &provided_1.compressed,
            mdoc_bytes,
            pkx,
            pky,
            transcript,
            &le_1970,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::PredicateNotSatisfied)
    );

    // 4. Negative Ge: birth_date >= 2000-01-01 (false since 1971-09-01 < 2000-01-01)
    let ge_2000 = [req_attr_ge(
        "org.iso.18013.5.1",
        "birth_date",
        *b"\xd9\x03\xec\x6a2000-01-01",
    )];
    assert_eq!(
        run_mdoc_prover_inner(
            &provided_1.spec,
            &provided_1.compressed,
            mdoc_bytes,
            pkx,
            pky,
            transcript,
            &ge_2000,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::PredicateNotSatisfied)
    );

    // 5. Negative: Le on non-date attribute (family_name) -> UnsupportedComparison
    let le_non_date = [req_attr_le(
        "org.iso.18013.5.1",
        "family_name",
        *b"\x6aMustermann",
    )];
    assert_eq!(
        run_mdoc_prover_inner(
            &provided_1.spec,
            &provided_1.compressed,
            mdoc_bytes,
            pkx,
            pky,
            transcript,
            &le_non_date,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::UnsupportedComparison)
    );
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_1.spec,
            &provided_1.compressed,
            pkx,
            pky,
            transcript,
            &le_non_date,
            now,
            doc_type,
            &proof_le,
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::UnsupportedComparison)
    );
}

fn run_current_pnym_tests(test_circuits: &TestCircuits) {
    let test_data = &mdoc_zk_testcases::vectors::PNYM_SEED_MDOC;
    let doc_type = test_data.doc_type;
    let now = test_data.now;
    let transcript = test_data.transcript;
    let seed = [0x42u8; 32];

    let provided_pnym = test_circuits.get_pnym().unwrap();
    let context = b"verifier.example.org/relying-party-session-2026";
    let pnym_req = [req_pnym("org.iso.18013.5.1", context)];

    let mut rng = runtime_random::DeterministicRng::new(99);
    let (proof_pnym, resolved_attrs) = run_mdoc_prover_inner_ext(
        &provided_pnym.spec,
        &provided_pnym.compressed,
        test_data.mdoc,
        test_data.pkx,
        test_data.pky,
        transcript,
        &pnym_req,
        now,
        doc_type,
        &mut rng,
    )
    .expect("Pseudonym prover should succeed");

    let expected_digest = mdoc_zk_circuits::cbor::compute_pseudonym(&seed, context);
    let expected_cbor = mdoc_zk_circuits::cbor::encode_pnym_cbor_value(&expected_digest);
    assert_eq!(resolved_attrs.len(), 1);
    assert_eq!(resolved_attrs[0].cbor_value, expected_cbor);

    // Bind prover response against verifier's own request using bind_pnym_response
    let bound_attrs = mdoc_zk_runtime::bind_pnym_response(&pnym_req, &resolved_attrs)
        .expect("bind_pnym_response should succeed on valid response");
    assert_eq!(bound_attrs, resolved_attrs);

    // Verify with bound_attrs
    run_mdoc_verifier_inner(
        &provided_pnym.spec,
        &provided_pnym.compressed,
        test_data.pkx,
        test_data.pky,
        transcript,
        &bound_attrs,
        now,
        doc_type,
        &proof_pnym,
    )
    .expect("Pseudonym verification should succeed");

    // Negative 1: Tampered pseudonym value -> GeneralFailure
    let mut bad_val_attrs = resolved_attrs.clone();
    bad_val_attrs[0].cbor_value[10] ^= 0x01;
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_pnym.spec,
            &provided_pnym.compressed,
            test_data.pkx,
            test_data.pky,
            transcript,
            &bad_val_attrs,
            now,
            doc_type,
            &proof_pnym,
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure)
    );

    // Negative 2: Tampered context -> GeneralFailure
    let mut bad_ctx_attrs = resolved_attrs.clone();
    bad_ctx_attrs[0].context = b"different-verifier-context".to_vec();
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_pnym.spec,
            &provided_pnym.compressed,
            test_data.pkx,
            test_data.pky,
            transcript,
            &bad_ctx_attrs,
            now,
            doc_type,
            &proof_pnym,
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::GeneralFailure)
    );
    // And bind_pnym_response preserves the verifier's own context even if the prover's
    // response mutated it.
    let rebound = mdoc_zk_runtime::bind_pnym_response(&pnym_req, &bad_ctx_attrs)
        .expect("bind_pnym_response keeps verifier's context");
    assert_eq!(rebound[0].context, context);

    // Negative 3: Missing context -> PnymContextMissing on prover, InvalidRequest on verifier
    let empty_ctx_req = [req_pnym("org.iso.18013.5.1", b"")];
    assert_eq!(
        run_mdoc_prover_inner_ext(
            &provided_pnym.spec,
            &provided_pnym.compressed,
            test_data.mdoc,
            test_data.pkx,
            test_data.pky,
            transcript,
            &empty_ctx_req,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::PnymContextMissing)
    );
    let mut empty_ctx_ver = resolved_attrs.clone();
    empty_ctx_ver[0].context.clear();
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_pnym.spec,
            &provided_pnym.compressed,
            test_data.pkx,
            test_data.pky,
            transcript,
            &empty_ctx_ver,
            now,
            doc_type,
            &proof_pnym,
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::InvalidRequest)
    );

    // Negative 4: Missing pnym_seed in mdoc -> PnymSeedMissing
    let mdoc_without_pnym = &mdoc_zk_testcases::vectors::PLUS_18_MDOC_0;
    assert_eq!(
        run_mdoc_prover_inner_ext(
            &provided_pnym.spec,
            &provided_pnym.compressed,
            mdoc_without_pnym.mdoc,
            mdoc_without_pnym.pkx,
            mdoc_without_pnym.pky,
            transcript,
            &pnym_req,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::PnymSeedMissing)
    );

    // Negative 5: Malformed pnym_seed in mdoc (change elementValue header from bstr(32) `0x58 0x20`
    // to tstr(32) `0x78 0x20`) -> PnymSeedMalformed
    let mut mdoc_bad_seed = test_data.mdoc.to_vec();
    let val_hdr_pos = mdoc_bad_seed
        .windows(b"\x6celementValue\x58\x20".len())
        .position(|w| w == b"\x6celementValue\x58\x20")
        .unwrap()
        + b"\x6celementValue".len();
    mdoc_bad_seed[val_hdr_pos] = 0x78;
    assert_eq!(
        run_mdoc_prover_inner_ext(
            &provided_pnym.spec,
            &provided_pnym.compressed,
            &mdoc_bad_seed,
            test_data.pkx,
            test_data.pky,
            transcript,
            &pnym_req,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::PnymSeedMalformed)
    );

    // Negative 6: pnym_seed with 32-byte random salt (131-byte IssuerSignedItem > 119 bytes)
    // must return Err(MdocProverErrorCode::AttributeTooLong) cleanly without panicking.
    let mut mdoc_32b_salt = test_data.mdoc.to_vec();
    let tag24_len_pos = mdoc_32b_salt
        .windows(4)
        .position(|w| w == [0xd8, 0x18, 0x58, 0x6e])
        .unwrap()
        + 3;
    mdoc_32b_salt[tag24_len_pos] += 17;
    let rand_hdr_pos = mdoc_32b_salt
        .windows(b"\x66random\x50".len())
        .position(|w| w == b"\x66random\x50")
        .unwrap()
        + b"\x66random".len();
    let mut expanded_rand = vec![0x58, 0x20];
    expanded_rand.extend_from_slice(&[0x42u8; 16]);
    mdoc_32b_salt.splice(rand_hdr_pos..rand_hdr_pos + 1, expanded_rand);
    assert_eq!(
        run_mdoc_prover_inner_ext(
            &provided_pnym.spec,
            &provided_pnym.compressed,
            &mdoc_32b_salt,
            test_data.pkx,
            test_data.pky,
            transcript,
            &pnym_req,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::AttributeTooLong)
    );
}

fn run_verifier_and_prover_input_vetting_tests(test_circuits: &TestCircuits) {
    let test_data = &mdoc_zk_testcases::vectors::BIRTHDATE_1971_09_01_MDOC_3;
    let doc_type = "org.iso.18013.5.1.mDL";
    let now = test_data.now;
    let transcript = test_data.transcript;
    let pkx = test_data.pkx;
    let pky = test_data.pky;
    let provided_1 = test_circuits.get(1).unwrap();
    let mut rng = runtime_random::DeterministicRng::new(77);

    let valid_attr = [req_attr(
        "org.iso.18013.5.1",
        "birth_date",
        *b"\xd9\x03\xec\x6a1971-09-01",
    )];

    // 1. Attribute whose minimum encoding `70 + cbor_id.len() + cbor_val.len()` exceeds
    //    `max_attr_cbor_len(2)` (119 bytes): id = 20 bytes -> cbor_id.len() = 21, and a
    //    34-byte bstr(32) value -> 70 + 21 + 34 = 125 > 119.
    let mut val_34 = vec![0x58, 0x20];
    val_34.extend_from_slice(&[0x11u8; 32]);
    let oversize_attr = [req_attr(
        "org.iso.18013.5.1",
        "twenty_char_attr_id_",
        &val_34,
    )];
    assert!(
        !mdoc_zk_runtime::attr_encoding_fits(
            b"twenty_char_attr_id_",
            &val_34,
            mdoc_zk_runtime::mso_attribute::constants::K_MAX_ATTR_SHA_BLOCKS,
        ),
        "125-byte minimum attribute encoding must not fit in 2 SHA-256 blocks (119 bytes)"
    );
    assert!(
        mdoc_zk_runtime::attr_encoding_fits(b"twenty_char_attr_id_", &val_34, 3),
        "125-byte minimum attribute encoding fits in 3 SHA-256 blocks (183 bytes)"
    );
    assert_eq!(
        run_mdoc_prover_inner(
            &provided_1.spec,
            &provided_1.compressed,
            test_data.mdoc,
            pkx,
            pky,
            transcript,
            &oversize_attr,
            now,
            doc_type,
            &mut rng,
        ),
        Err(mdoc_zk_runtime::MdocProverErrorCode::AttributeTooLong)
    );
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_1.spec,
            &provided_1.compressed,
            pkx,
            pky,
            transcript,
            &oversize_attr,
            now,
            doc_type,
            &[0u8; 100],
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::UnsupportedAttribute)
    );

    // 2. Malformed `now` timestamp (wrong length or non-ISO-8601 format) -> InvalidInput
    for bad_now in [
        "2025-04-30",
        "2025-04-30T00:00:00Z_extra",
        "2025/04/30T00:00:00Z",
    ] {
        assert_eq!(
            run_mdoc_verifier_inner(
                &provided_1.spec,
                &provided_1.compressed,
                pkx,
                pky,
                transcript,
                &valid_attr,
                bad_now,
                doc_type,
                &[0u8; 100],
            ),
            Err(mdoc_zk_runtime::MdocVerifierErrorCode::InvalidInput)
        );
    }

    // 3. Oversize `doc_type` (> 32 bytes) -> InvalidInput
    let long_doc_type = "org.iso.18013.5.1.mDL.extra.long.doctype";
    assert!(long_doc_type.len() > 32);
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_1.spec,
            &provided_1.compressed,
            pkx,
            pky,
            transcript,
            &valid_attr,
            now,
            long_doc_type,
            &[0u8; 100],
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::InvalidInput)
    );

    // 4. Malformed `pkx` / `pky` (empty or non-hex) -> InvalidInput before circuit decompression
    for bad_pk in ["", "0x", "0xzzzz"] {
        assert_eq!(
            run_mdoc_verifier_inner(
                &provided_1.spec,
                &provided_1.compressed,
                bad_pk,
                pky,
                transcript,
                &valid_attr,
                now,
                doc_type,
                &[0u8; 100],
            ),
            Err(mdoc_zk_runtime::MdocVerifierErrorCode::InvalidInput)
        );
    }

    // 5. Non-ISO-8601 date characters inside 14-byte tag(1004) with Le/Ge -> UnsupportedComparison
    let non_iso_date = [req_attr_le(
        "org.iso.18013.5.1",
        "birth_date",
        *b"\xd9\x03\xec\x6a2000/01/01",
    )];
    assert_eq!(
        run_mdoc_verifier_inner(
            &provided_1.spec,
            &provided_1.compressed,
            pkx,
            pky,
            transcript,
            &non_iso_date,
            now,
            doc_type,
            &[0u8; 100],
        ),
        Err(mdoc_zk_runtime::MdocVerifierErrorCode::UnsupportedComparison)
    );
}

#[test]
fn test_all_current_zk() {
    let test_circuits = TestCircuits::compile_all();
    run_current_circuit_hashes(&test_circuits);
    run_current_mdoc_flow(&test_circuits);
    run_current_mdoc_subset_flow(&test_circuits);
    run_current_mdoc_all_positive_cases(&test_circuits);
    run_current_mdoc_all_negative_cases(&test_circuits);
    run_current_verifier_negative_cases(&test_circuits);
    run_current_verifier_attribute_reordering_and_duplicates(&test_circuits);
    run_current_verifier_bad_proofs(&test_circuits);
    run_circuit_supports_cbor();
    run_namespace_mixup(&test_circuits);
    run_current_date_comparison_tests(&test_circuits);
    run_current_pnym_tests(&test_circuits);
    run_verifier_and_prover_input_vetting_tests(&test_circuits);
}
