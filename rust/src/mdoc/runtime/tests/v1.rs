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

//! Longfellow v1 application compatibility and failure cases.

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use sha2::{Digest, Sha256};

    use crate::{
        compile::algebra::CompileNat,
        mdoc::{circuits::parse_test_data, v1::*},
    };

    fn is_supported_by_prior_version<N>(
        spec: &ZkSpecStruct,
        parsed: &crate::mdoc::circuits::cbor::mdoc::ParsedMdoc<N>,
    ) -> bool {
        if spec.version <= 7 {
            let max_mso_blocks = if spec.version <= 6 { 35 } else { 40 };
            if parsed.cbor_mso.len() + 9 > max_mso_blocks * 64 {
                return false;
            }
            if parsed
                .attrs
                .iter()
                .take(spec.num_attributes)
                .any(|a| a.cbor_issuer_signed_item.len() + 9 > 2 * 64)
            {
                return false;
            }
        }
        if spec.version < 7
            && parsed.attrs.iter().take(spec.num_attributes).any(|a| {
                let slot_elem_i = (a.field_locator.permutation >> 4) & 3;
                let slot_elem_v = (a.field_locator.permutation >> 6) & 3;
                slot_elem_i != 2 || slot_elem_v != 3
            })
        {
            return false;
        }
        true
    }

    #[test]
    fn test_circuit_ids_match_zkspecs() {
        let p256 = crate::runtime::algebra::p256::P256Field::new();
        let gf2 = crate::runtime::algebra::gf2_128::Gf2_128Field::new();

        for (version, nattrs) in provider::registered_versions_and_attrs() {
            let provided = provider::materialize(version, nattrs).expect("Failed to materialize");
            let spec = &provided.spec;
            let compressed = &provided.compressed;
            let (c_sig, c_hash) = decompress_circuits(compressed, &p256, &gf2)
                .expect("Failed to decompress circuits");
            println!(
                "Circuit {} (v{}, {} attrs): sig_npub = {}, hash_npub = {}",
                provided.name,
                spec.version,
                spec.num_attributes,
                c_sig.raw.npublic_input,
                c_hash.raw.npublic_input
            );

            let sig_id = crate::core::proto::v1::compute_id(&p256, &c_sig.raw);
            assert_eq!(
                sig_id, c_sig.id,
                "Signature ID mismatch for {}",
                provided.name
            );

            let hash_id = crate::core::proto::v1::compute_id(&gf2, &c_hash.raw);
            assert_eq!(hash_id, c_hash.id, "Hash ID mismatch for {}", provided.name);

            let mut hasher = Sha256::new();
            hasher.update(sig_id);
            hasher.update(hash_id);
            let overall_id = hasher.finalize();

            let mut hex_str = String::with_capacity(64);
            for byte in overall_id {
                write!(&mut hex_str, "{byte:02x}").unwrap();
            }
            assert_eq!(
                hex_str,
                spec.combined_hash_hex(),
                "Overall circuit hash mismatch for spec {spec:?}"
            );
        }
    }

    #[test]
    fn test_all_circuits_prior_compatibility() {
        let test_data = &crate::mdoc::testcases::vectors::BIRTHDATE_1971_09_01_MDOC_3;
        let all_attrs = [
            req_attr(
                "org.iso.18013.5.1",
                "family_name",
                [
                    0x6a, b'M', b'u', b's', b't', b'e', b'r', b'm', b'a', b'n', b'n',
                ],
            ),
            req_attr(
                "org.iso.18013.5.1",
                "birth_date",
                [
                    0xd9, 0x03, 0xec, 0x6a, b'1', b'9', b'7', b'1', b'-', b'0', b'9', b'-', b'0',
                    b'1',
                ],
            ),
            req_attr(
                "org.iso.18013.5.1",
                "issue_date",
                [
                    0xd9, 0x03, 0xec, 0x6a, b'2', b'0', b'2', b'4', b'-', b'0', b'3', b'-', b'1',
                    b'5',
                ],
            ),
            req_attr("org.iso.18013.5.1", "height", [0x18, 0xaf]),
        ];

        let attrs_ref = &all_attrs;
        let checked = std::sync::atomic::AtomicUsize::new(0);
        let checked_ref = &checked;
        std::thread::scope(|s| {
            for version in [5, 6, 7] {
                for nattrs in 1..=4 {
                    s.spawn(move || {
                        let provided = provider::materialize(version, nattrs).unwrap();
                        let spec = &provided.spec;
                        let hash_hex = spec.combined_hash_hex();
                        let compressed = &provided.compressed;
                        let expected_prior_proof =
                            crate::mdoc::artifacts::load_prior_proof(&hash_hex);

                        let attrs = &attrs_ref[..spec.num_attributes];

                        let parsed: crate::mdoc::circuits::cbor::mdoc::ParsedMdoc<CompileNat<4>> =
                            crate::mdoc::circuits::cbor::mdoc::parse_mdoc(
                                test_data.mdoc,
                                test_data.transcript,
                                "org.iso.18013.5.1.mDL",
                            )
                            .expect("test fixture must contain a valid mdoc");

                        assert!(
                            is_supported_by_prior_version(spec, &parsed),
                            "saved-proof fixture must run for v{version}, {nattrs} attributes"
                        );

                        // Verify the saved legacy proof as well as a newly generated one.
                        // A prover/verifier roundtrip alone can hide a matching protocol change.
                        crate::mdoc::v1::verifier::run_mdoc_verifier(
                            spec,
                            compressed,
                            test_data.pkx,
                            test_data.pky,
                            test_data.transcript,
                            attrs,
                            test_data.now,
                            "org.iso.18013.5.1.mDL",
                            &expected_prior_proof,
                        )
                        .expect("saved legacy proof must verify");

                        let mut rng = crate::runtime::random::DeterministicRng::new(42);

                        let proof_bytes = crate::mdoc::v1::prover::run_mdoc_prover_inner(
                            spec,
                            compressed,
                            test_data.mdoc,
                            test_data.pkx,
                            test_data.pky,
                            test_data.transcript,
                            attrs,
                            test_data.now,
                            "org.iso.18013.5.1.mDL",
                            &mut rng,
                        )
                        .expect("prover failed");

                        assert!(
                            proof_bytes == expected_prior_proof,
                            "legacy proof bytes changed for v{version}, {nattrs} attributes: first difference {:?}, actual {} bytes, expected {} bytes",
                            proof_bytes.iter().zip(&expected_prior_proof).position(|(a, b)| a != b),
                            proof_bytes.len(),
                            expected_prior_proof.len(),
                        );

                        crate::mdoc::v1::verifier::run_mdoc_verifier(
                            spec,
                            compressed,
                            test_data.pkx,
                            test_data.pky,
                            test_data.transcript,
                            attrs,
                            test_data.now,
                            "org.iso.18013.5.1.mDL",
                            &proof_bytes,
                        )
                        .expect("verifier failed");
                        checked_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    });
                }
            }
        });
        assert_eq!(checked.load(std::sync::atomic::Ordering::Relaxed), 12);
    }

    #[test]
    fn test_all_circuits_all_test_cases() {
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::scope(|s| {
            for (version, nattrs) in provider::registered_versions_and_attrs() {
                let tx_thread = tx.clone();
                s.spawn(move || {
                    let provided = provider::materialize(version, nattrs)
                        .expect("Failed to materialize circuit");
                    let spec = &provided.spec;
                    let compressed = &provided.compressed;
                    let mut count = 0;

                    for case in crate::mdoc::testcases::vectors::ALL_TEST_CASES {
                        if case.name.starts_with("fail-") {
                            continue;
                        }
                        let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(case.data);
                        if parsed.attrs.len() < spec.num_attributes {
                            continue;
                        }
                        if !is_supported_by_prior_version(spec, &parsed) {
                            continue;
                        }

                        println!(
                            "Testing circuit {} (v{}, {} attrs) with test case {}",
                            provided.name, spec.version, spec.num_attributes, case.name
                        );

                        let ns = if case.data.doc_type.starts_with("org.iso.18013.5.1") {
                            "org.iso.18013.5.1"
                        } else {
                            case.data.doc_type
                        };
                        let req_attrs: Vec<RequestedAttribute> = parsed
                            .attrs
                            .iter()
                            .take(spec.num_attributes)
                            .map(|a| req_attr(ns, &a.name, &a.cbor_value))
                            .collect();

                        let mut rng = crate::runtime::random::DeterministicRng::new(42);
                        let prove_res = run_mdoc_prover_inner(
                            spec,
                            compressed,
                            case.data.mdoc,
                            case.data.pkx,
                            case.data.pky,
                            case.data.transcript,
                            &req_attrs,
                            now,
                            case.data.doc_type,
                            &mut rng,
                        );
                        assert!(
                            prove_res.is_ok(),
                            "Prover failed for circuit {} on test case {}: {:?}",
                            provided.name,
                            case.name,
                            prove_res.err()
                        );
                        let proof = prove_res.unwrap();

                        let verify_res = run_mdoc_verifier_inner(
                            spec,
                            compressed,
                            case.data.pkx,
                            case.data.pky,
                            case.data.transcript,
                            &req_attrs,
                            now,
                            case.data.doc_type,
                            &proof,
                        );
                        assert!(
                            verify_res.is_ok(),
                            "Verifier failed for circuit {} on test case {}: {:?}",
                            provided.name,
                            case.name,
                            verify_res.err()
                        );
                        count += 1;
                    }
                    tx_thread.send(count).unwrap();
                });
            }
        });
        drop(tx);
        let total_count: usize = rx.iter().sum();
        println!("Successfully executed {total_count} prover/verifier combinations across v1 circuits v5, v6 and v7!");
        assert!(total_count > 0);
    }
}
