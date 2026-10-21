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

use circuits_bitvec::{Bitvec, BitvecLogic};
use circuits_boolean::Boolean;
use compile_algebra::{field::CompileField, gf2_128::Gf2_128Field, p256::P256Field, CompileNat};
use compile_logic::{eval::EvalLogic, Logic};
use core_algebra::Nat;
use mdoc_zk_circuits::{
    hash::{
        circuit::DisclosedAttribute, derived, evaluate_derived, evaluate_given, given,
        hash_input_of_parsed_mdoc, HashMac, MdocHash,
    },
    mso_attribute::constants::K_ATTR_INDEX_BITS,
    parse_test_data,
};

use super::mdoc_hash_corruptors;

#[test]
fn test_eval_mdoc_hash_independent() {
    let fc = P256Field::new();
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);

    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&fc, &tracker);

    let mac_input = HashMac {
        mac_av: 0,
        mac_ap: [[0, 0]; 3],
    };
    let given = given::<4, _>(hash_input, mac_input);
    let derived = derived::<4, _>(&given);
    let mdoc = MdocHash::new(&l, given.hash_input.attrs.len());
    let bv = BitvecLogic::new(&l);
    let wire_given = evaluate_given(&l, &bv, &given);
    let wire_derived = evaluate_derived(&l, &bv, &derived);

    let assertion = mdoc.assert_valid_presentation_and_macs(&wire_given, &wire_derived);
    assertion.unwrap();
}

fn test_eval_mdoc_hash_generic<'a, const W: usize, FC>(l: &'a EvalLogic<'a, FC>)
where FC: CompileField + circuits_analog_adder::FieldWrappingSum {
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);

    let mac_input = HashMac {
        mac_av: 0,
        mac_ap: [[0, 0]; 3],
    };
    let given = given::<4, _>(hash_input, mac_input);
    let derived = derived::<4, _>(&given);
    let bv = BitvecLogic::new(l);
    let wire_given = evaluate_given(l, &bv, &given);
    let wire_derived = evaluate_derived(l, &bv, &derived);

    let mdoc = MdocHash::new(l, given.hash_input.attrs.len());
    let assertion = mdoc.assert_valid_presentation(&wire_given, &wire_derived);

    assertion.unwrap();
}

fn test_eval_mdoc_hash_with_mac_generic<'a, const W: usize, FC>(l: &'a EvalLogic<'a, FC>)
where FC: CompileField + circuits_analog_adder::FieldWrappingSum {
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);

    let av_u128 = 0x112233445566778899aabbccddeeff00u128;
    let ap0_u128 = 0xabcdef0123456789abcdef0123456789u128;
    let ap1_u128 = 0xfedcba9876543210fedcba9876543210u128;
    let ap_keys = [[ap0_u128, ap1_u128]; 3];

    let mac_input = HashMac {
        mac_av: av_u128,
        mac_ap: ap_keys,
    };
    let given = given::<4, _>(hash_input, mac_input);
    let derived = derived::<4, _>(&given);
    let bv = BitvecLogic::new(l);
    let wire_given = evaluate_given(l, &bv, &given);
    let wire_derived = evaluate_derived(l, &bv, &derived);

    let mdoc = MdocHash::new(l, given.hash_input.attrs.len());
    let assertion = mdoc.assert_valid_presentation_and_macs(&wire_given, &wire_derived);

    assertion.unwrap();
}

#[test]
fn test_eval_mdoc_hash() {
    let f = Gf2_128Field::new();
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    test_eval_mdoc_hash_generic::<2, _>(&l);
}

#[test]
fn test_eval_mdoc_hash_with_mac() {
    let f = Gf2_128Field::new();
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    test_eval_mdoc_hash_with_mac_generic::<2, _>(&l);
}

fn apply_negative_test_modifications<'a, FC: CompileField>(
    filename: &str,
    disclosed_attrs: &mut [DisclosedAttribute<EvalLogic<'a, FC>>],
    logic: &EvalLogic<'a, FC>,
    bitvec_logic: &BitvecLogic<EvalLogic<'a, FC>>,
) {
    let boolean = Boolean::new(logic);

    let eval_bitvec_u8 = |bv: &Bitvec<EvalLogic<'a, FC>, 8>| -> u8 {
        let mut val = 0u8;
        for i in 0..8 {
            let bit_eltw = bv.bit(i);
            let eltw = boolean.as_eltw(bit_eltw);
            if eltw.value != logic.field().zero() {
                val |= 1 << i;
            }
        }
        val
    };

    if filename.contains("fail-not_over_18") {
        let target_key = b"age_over_18";
        let mut target_cbor_key = vec![0x60 + target_key.len() as u8];
        target_cbor_key.extend_from_slice(target_key);

        for da in disclosed_attrs.iter_mut() {
            let mut key_bytes = [0u8; 32];
            for (byte, val) in key_bytes.iter_mut().zip(da.expected_name.data.iter()) {
                *byte = eval_bitvec_u8(val);
            }
            if key_bytes.starts_with(&target_cbor_key) {
                da.expected_cbor_value.data[0] = bitvec_logic.of_u8(0xf4);
                for j in 1..da.expected_cbor_value.data.len() {
                    da.expected_cbor_value.data[j] = bitvec_logic.of_u8(0);
                }
                da.expected_cbor_value.len = bitvec_logic.of_u64::<K_ATTR_INDEX_BITS>(1);
            }
        }
    } else if filename.contains("fail-birthdate_0971_09_01") {
        let target_key = b"birth_date";
        let mut target_cbor_key = vec![0x60 + target_key.len() as u8];
        target_cbor_key.extend_from_slice(target_key);

        for da in disclosed_attrs.iter_mut() {
            let mut key_bytes = [0u8; 32];
            for (byte, val) in key_bytes.iter_mut().zip(da.expected_name.data.iter()) {
                *byte = eval_bitvec_u8(val);
            }
            if key_bytes.starts_with(&target_cbor_key) {
                let mut val = vec![0xD9, 0x03, 0xEC, 0x6A];
                val.extend_from_slice(b"0971-09-01");
                for (dst, &src) in da.expected_cbor_value.data.iter_mut().zip(val.iter()) {
                    *dst = bitvec_logic.of_u8(src);
                }
                for i in val.len()..da.expected_cbor_value.data.len() {
                    da.expected_cbor_value.data[i] = bitvec_logic.of_u8(0);
                }
                da.expected_cbor_value.len =
                    bitvec_logic.of_u64::<K_ATTR_INDEX_BITS>(val.len() as u64);
            }
        }
    } else if filename.contains("fail-birthdate_1871_09_01") {
        let target_key = b"birth_date";
        let mut target_cbor_key = vec![0x60 + target_key.len() as u8];
        target_cbor_key.extend_from_slice(target_key);

        for da in disclosed_attrs.iter_mut() {
            let mut key_bytes = [0u8; 32];
            for (byte, val) in key_bytes.iter_mut().zip(da.expected_name.data.iter()) {
                *byte = eval_bitvec_u8(val);
            }
            if key_bytes.starts_with(&target_cbor_key) {
                let mut val = vec![0xD9, 0x03, 0xEC, 0x6A];
                val.extend_from_slice(b"1871-09-01");
                for (dst, &src) in da.expected_cbor_value.data.iter_mut().zip(val.iter()) {
                    *dst = bitvec_logic.of_u8(src);
                }
                for i in val.len()..da.expected_cbor_value.data.len() {
                    da.expected_cbor_value.data[i] = bitvec_logic.of_u8(0);
                }
                da.expected_cbor_value.len =
                    bitvec_logic.of_u64::<K_ATTR_INDEX_BITS>(val.len() as u64);
            }
        }
    } else if filename.contains("fail-birthdate_1971_09_01_extra_0") {
        let target_key = b"birth_date";
        let mut target_cbor_key = vec![0x60 + target_key.len() as u8];
        target_cbor_key.extend_from_slice(target_key);

        for da in disclosed_attrs.iter_mut() {
            let mut key_bytes = [0u8; 32];
            for (byte, val) in key_bytes.iter_mut().zip(da.expected_name.data.iter()) {
                *byte = eval_bitvec_u8(val);
            }
            if key_bytes.starts_with(&target_cbor_key) {
                let mut val = vec![0xD9, 0x03, 0xEC, 0x6A];
                val.extend_from_slice(b"1971-09-010");
                for (dst, &src) in da.expected_cbor_value.data.iter_mut().zip(val.iter()) {
                    *dst = bitvec_logic.of_u8(src);
                }
                for i in val.len()..da.expected_cbor_value.data.len() {
                    da.expected_cbor_value.data[i] = bitvec_logic.of_u8(0);
                }
                da.expected_cbor_value.len =
                    bitvec_logic.of_u64::<K_ATTR_INDEX_BITS>(val.len() as u64);
            }
        }
    }
}

fn test_all_mdoc_cases_generic<'a, const W: usize, FC>(l: &'a EvalLogic<'a, FC>)
where FC: CompileField + circuits_analog_adder::FieldWrappingSum {
    let mut count = 0;

    for case in mdoc_zk_testcases::vectors::ALL_TEST_CASES {
        let filename = case.name;
        println!("Running test case: {filename}");
        let is_negative = filename.starts_with("fail-");

        let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(case.data);
        let hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);

        let mac_input = HashMac {
            mac_av: 0,
            mac_ap: [[0, 0]; 3],
        };
        let given = given::<4, _>(hash_input, mac_input);
        let derived = derived::<4, _>(&given);
        let bitvec_logic = BitvecLogic::new(l);
        let mut wire_given = evaluate_given(l, &bitvec_logic, &given);
        let wire_derived = evaluate_derived(l, &bitvec_logic, &derived);

        apply_negative_test_modifications(
            filename,
            &mut wire_given.disclosed_attributes,
            l,
            &bitvec_logic,
        );

        let mdoc = MdocHash::new(l, given.hash_input.attrs.len());
        let assertion = mdoc.assert_valid_presentation(&wire_given, &wire_derived);
        if is_negative {
            assert!(
                assertion.is_err(),
                "Expected negative test to fail: {filename}"
            );
        } else {
            assertion.unwrap();
        }
        count += 1;
    }
    assert!(count > 0, "No test cases found/executed!");
    println!("Successfully verified {count} test cases.");
}

#[test]
fn test_all_mdoc_cases() {
    let f = Gf2_128Field::new();
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    test_all_mdoc_cases_generic::<2, _>(&l);
}

#[test]
fn test_namespace_mixup_exploit() {
    let f = Gf2_128Field::new();

    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let mut hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);

    let doc_type_off = 23 + parsed.doc_type_offset_in_mso;
    hash_input.cbor_mso[doc_type_off] ^= 1;

    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(&hash_input.cbor_mso);
    let sha_result = hasher.finalize();

    hash_input.issuer_sig_e = CompileNat::<4>::from_bytes_be(&sha_result);

    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);

    let mac_input = HashMac {
        mac_av: 0,
        mac_ap: [[0, 0]; 3],
    };
    let given = given::<4, _>(hash_input, mac_input);
    let derived = derived::<4, _>(&given);
    let bv = BitvecLogic::new(&l);
    let mut tampered_given = given.clone();
    tampered_given.doc_type_offset_in_preimage += 1;

    let wire_given = evaluate_given(&l, &bv, &tampered_given);
    let wire_derived = evaluate_derived(&l, &bv, &derived);

    let mdoc = MdocHash::new(&l, tampered_given.hash_input.attrs.len());
    let res = mdoc.assert_valid_presentation(&wire_given, &wire_derived);

    assert!(
        res.is_err(),
        "Expected tampered namespace/docType to fail circuit evaluation"
    );
    res.assert_any_failed_at(
        "assert_valid_presentation/assert_mso_doc_type/cbor_header/cbor_header.0/header_byte",
    );
}

#[test]
fn test_eval_mdoc_hash_shared_corruptors() {
    let f = Gf2_128Field::new();

    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let base_hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);
    let base_mac_input = HashMac {
        mac_av: 0x112233445566778899aabbccddeeff00u128,
        mac_ap: [
            [
                0xabcdef0123456789abcdef0123456789u128,
                0xfedcba9876543210fedcba9876543210u128,
            ],
            [
                0xabcdef0123456789abcdef0123456789u128,
                0xfedcba9876543210fedcba9876543210u128,
            ],
            [
                0xabcdef0123456789abcdef0123456789u128,
                0xfedcba9876543210fedcba9876543210u128,
            ],
        ],
    };

    let corruptors = mdoc_hash_corruptors::all_mdoc_hash_corruptors();
    for c in corruptors {
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let l = EvalLogic::new_with_tracker(&f, &tracker);
        let bv = BitvecLogic::new(&l);
        let base_given = given::<4, _>(base_hash_input.clone(), base_mac_input.clone());
        let derived_val = derived::<4, _>(&base_given);

        let mut tampered_given = base_given.clone();
        (c.corrupt)(&mut tampered_given);

        let wire_given = evaluate_given(&l, &bv, &tampered_given);
        let wire_derived = evaluate_derived(&l, &bv, &derived_val);

        let mdoc = MdocHash::new(&l, tampered_given.hash_input.attrs.len());
        let res = mdoc.assert_valid_presentation_and_macs(&wire_given, &wire_derived);
        assert!(
            res.is_err(),
            "Corruptor '{}' failed to cause assertion error",
            c.name
        );
        let failed = res.failed_paths();
        assert!(
            failed.iter().any(|path| path == &c.expected_path),
            "Corruptor '{}' expected exact failure path '{}', actual failures: {failed:?}",
            c.name,
            c.expected_path
        );
        res.assert_any_failed_at(&c.expected_path);
    }
}

#[test]
fn test_check_doc_type_suppression() {
    let f = Gf2_128Field::new();
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    let bv = BitvecLogic::new(&l);

    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);

    // 1. When suppress_doc_type_check is false and expected_doc_type matches, evaluation succeeds.
    let mut hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);
    hash_input.suppress_doc_type_check = false;
    hash_input.expected_doc_type = b"org.iso.18013.5.1.mDL".to_vec();

    let mac_input = HashMac {
        mac_av: 0,
        mac_ap: [[0, 0]; 3],
    };
    let given_val = given::<4, _>(hash_input.clone(), mac_input.clone());
    let derived_val = derived::<4, _>(&given_val);
    let wire_given = evaluate_given(&l, &bv, &given_val);
    let wire_derived = evaluate_derived(&l, &bv, &derived_val);
    let mdoc = MdocHash::new(&l, given_val.hash_input.attrs.len());
    let res = mdoc.assert_valid_presentation(&wire_given, &wire_derived);
    res.unwrap();

    // 2. When suppress_doc_type_check is false and expected_doc_type is wrong, evaluation fails.
    let mut wrong_hash_input = hash_input.clone();
    wrong_hash_input.expected_doc_type = b"wrong.doc.type.foo.bar".to_vec();
    let given_wrong = given::<4, _>(wrong_hash_input, mac_input.clone());

    let tracker2 = compile_logic::tracker::AssertionTracker::new();
    let l2 = EvalLogic::new_with_tracker(&f, &tracker2);
    let bv2 = BitvecLogic::new(&l2);

    let wire_given_wrong = evaluate_given(&l2, &bv2, &given_wrong);
    let wire_derived_wrong = evaluate_derived(&l2, &bv2, &derived_val);

    let mdoc2 = MdocHash::new(&l2, given_wrong.hash_input.attrs.len());
    let res_wrong =
        mdoc2.assert_valid_presentation_and_macs(&wire_given_wrong, &wire_derived_wrong);
    assert!(res_wrong.is_err());
    let failed_all = res_wrong.failed_paths();
    println!("ALL FAILED PATHS: {:?}", failed_all);
    res_wrong.assert_any_failed_at(
        "assert_valid_presentation_and_macs/assert_valid_presentation/assert_mso_doc_type/value_bytes/value_bytes.0/doc_type_byte"
    );

    // 3. When suppress_doc_type_check is true, even with wrong expected_doc_type, evaluation
    //    succeeds (check suppressed).
    let mut suppressed_hash_input = hash_input.clone();
    suppressed_hash_input.suppress_doc_type_check = true;
    suppressed_hash_input.expected_doc_type = b"wrong.doc.type.foo.bar".to_vec();
    let given_suppressed = given::<4, _>(suppressed_hash_input, mac_input);
    let tracker3 = compile_logic::tracker::AssertionTracker::new();
    let l3 = EvalLogic::new_with_tracker(&f, &tracker3);
    let bv3 = BitvecLogic::new(&l3);

    let wire_given_suppressed = evaluate_given(&l3, &bv3, &given_suppressed);
    let wire_derived_suppressed = evaluate_derived(&l3, &bv3, &derived_val);
    let mdoc3 = MdocHash::new(&l3, given_suppressed.hash_input.attrs.len());
    let res_suppressed =
        mdoc3.assert_valid_presentation(&wire_given_suppressed, &wire_derived_suppressed);
    res_suppressed.unwrap();
}

#[test]
fn test_eval_mdoc_hash_date_comparison() {
    let f = Gf2_128Field::new();
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(
        &mdoc_zk_testcases::vectors::BIRTHDATE_1971_09_01_MDOC_3,
    );
    let base_hash_input = hash_input_of_parsed_mdoc(&parsed, &[b"birth_date"], now);
    let mac_input = HashMac {
        mac_av: 0,
        mac_ap: [[0, 0]; 3],
    };

    let make_full_date = |s: &[u8; 10]| -> Vec<u8> {
        let mut v = vec![0xd9, 0x03, 0xec, 0x6a];
        v.extend_from_slice(s);
        v
    };

    // mdoc birth_date is 1971-09-01
    for (op, date_str, should_pass) in [
        (1u8, b"1971-09-01", true),
        (1u8, b"1971-09-02", true),
        (1u8, b"2007-09-01", true),
        (1u8, b"1971-08-31", false),
        (2u8, b"1971-09-01", true),
        (2u8, b"1971-08-31", true),
        (2u8, b"1971-09-02", false),
    ] {
        let mut hi = base_hash_input.clone();
        hi.attrs[0].op = op;
        hi.attrs[0].expected_cbor_value = make_full_date(date_str);

        let tracker = compile_logic::tracker::AssertionTracker::new();
        let l = EvalLogic::new_with_tracker(&f, &tracker);
        let bv = BitvecLogic::new(&l);
        let given_val = given::<4, _>(hi, mac_input.clone());
        let derived_val = derived::<4, _>(&given_val);
        let wg = evaluate_given(&l, &bv, &given_val);
        let wd = evaluate_derived(&l, &bv, &derived_val);
        let mdoc = MdocHash::new(&l, 1);
        let res = mdoc.assert_valid_presentation(&wg, &wd);
        assert_eq!(res.is_ok(), should_pass);
    }
}

#[test]
fn test_eval_mdoc_hash_pnym() {
    use mdoc_zk_circuits::hash::pnym_hash_input_of_parsed_mdoc;

    let f = Gf2_128Field::new();
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::PNYM_SEED_MDOC);

    let context = b"relying-party.example/ctx";
    let hi = pnym_hash_input_of_parsed_mdoc(&parsed, &[b"age_over_18"], context, now);
    let pnym_cbor = &hi.pnym.as_ref().unwrap().expected_cbor_value;
    assert_eq!(pnym_cbor.len(), 34);
    assert_eq!(&pnym_cbor[0..2], &[0x58, 0x20]);

    let mac_input = HashMac {
        mac_av: 0x112233445566778899aabbccddeeff00u128,
        mac_ap: [[0xabcdef, 0x123456]; 3],
    };
    let given_val = given::<4, _>(hi, mac_input);
    let derived_val = derived::<4, _>(&given_val);

    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    let bv = BitvecLogic::new(&l);
    let wg = evaluate_given(&l, &bv, &given_val);
    let wd = evaluate_derived(&l, &bv, &derived_val);
    let mdoc = MdocHash::with_pnym(&l, 1, true);
    mdoc.assert_valid_presentation_and_macs(&wg, &wd).unwrap();
}

#[test]
fn test_eval_mdoc_hash_1attr_pnym_ops() {
    use mdoc_zk_circuits::hash::pnym_hash_input_of_parsed_mdoc;

    let f = Gf2_128Field::new();
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::PNYM_SEED_MDOC);
    let context = b"verifier.example.org/relying-party-session-2026";
    let mac_input = HashMac {
        mac_av: 0x112233445566778899aabbccddeeff00u128,
        mac_ap: [[0xabcdef, 0x123456]; 3],
    };

    // 1. Positive Le comparison (birth_date <= 2000-01-01) + pseudonym in (1, true)
    let mut hi_le = pnym_hash_input_of_parsed_mdoc(&parsed, &[b"birth_date"], context, now);
    hi_le.attrs[0].op = 1; // Le
    hi_le.attrs[0].expected_cbor_value = b"\xd9\x03\xec\x6a2000-01-01".to_vec();
    {
        let given_val = given::<4, _>(hi_le.clone(), mac_input.clone());
        let derived_val = derived::<4, _>(&given_val);
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let l = EvalLogic::new_with_tracker(&f, &tracker);
        let bv = BitvecLogic::new(&l);
        let wg = evaluate_given(&l, &bv, &given_val);
        let wd = evaluate_derived(&l, &bv, &derived_val);
        let mdoc = MdocHash::with_pnym(&l, 1, true);
        mdoc.assert_valid_presentation_and_macs(&wg, &wd).unwrap();
    }

    // 2. Positive Ge comparison (birth_date >= 1970-01-01) + pseudonym in (1, true)
    let mut hi_ge = pnym_hash_input_of_parsed_mdoc(&parsed, &[b"birth_date"], context, now);
    hi_ge.attrs[0].op = 2; // Ge
    hi_ge.attrs[0].expected_cbor_value = b"\xd9\x03\xec\x6a1970-01-01".to_vec();
    {
        let given_val = given::<4, _>(hi_ge, mac_input.clone());
        let derived_val = derived::<4, _>(&given_val);
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let l = EvalLogic::new_with_tracker(&f, &tracker);
        let bv = BitvecLogic::new(&l);
        let wg = evaluate_given(&l, &bv, &given_val);
        let wd = evaluate_derived(&l, &bv, &derived_val);
        let mdoc = MdocHash::with_pnym(&l, 1, true);
        mdoc.assert_valid_presentation_and_macs(&wg, &wd).unwrap();
    }

    // 3. Negative: regular attribute fails Eq (age_over_18 claimed false) while pseudonym is valid
    let mut hi_bad_attr = pnym_hash_input_of_parsed_mdoc(&parsed, &[b"age_over_18"], context, now);
    hi_bad_attr.attrs[0].expected_cbor_value = vec![0xf4];
    {
        let given_val = given::<4, _>(hi_bad_attr, mac_input.clone());
        let derived_val = derived::<4, _>(&given_val);
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let l = EvalLogic::new_with_tracker(&f, &tracker);
        let bv = BitvecLogic::new(&l);
        let wg = evaluate_given(&l, &bv, &given_val);
        let wd = evaluate_derived(&l, &bv, &derived_val);
        let mdoc = MdocHash::with_pnym(&l, 1, true);
        let res = mdoc.assert_valid_presentation_and_macs(&wg, &wd);
        assert!(res.is_err());
        res.assert_any_failed_at(
            "assert_valid_presentation_and_macs/assert_valid_presentation/assert_attributes/assert_attributes.0/attribute_item/assert_attribute/assert_item_slot_key_value/value_rel_ok",
        );
    }

    // 4. Negative: regular attribute passes, but pseudonym value is tampered
    let mut hi_bad_pnym = pnym_hash_input_of_parsed_mdoc(&parsed, &[b"age_over_18"], context, now);
    hi_bad_pnym.pnym.as_mut().unwrap().expected_cbor_value[2] ^= 0x80;
    {
        let given_val = given::<4, _>(hi_bad_pnym, mac_input.clone());
        let derived_val = derived::<4, _>(&given_val);
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let l = EvalLogic::new_with_tracker(&f, &tracker);
        let bv = BitvecLogic::new(&l);
        let wg = evaluate_given(&l, &bv, &given_val);
        let wd = evaluate_derived(&l, &bv, &derived_val);
        let mdoc = MdocHash::with_pnym(&l, 1, true);
        let res = mdoc.assert_valid_presentation_and_macs(&wg, &wd);
        assert!(res.is_err());
    }

    // 5. Negative: regular attribute passes, but public pseudonym context is tampered
    let hi_ok = pnym_hash_input_of_parsed_mdoc(&parsed, &[b"age_over_18"], context, now);
    {
        let mut given_val = given::<4, _>(hi_ok, mac_input);
        let derived_val = derived::<4, _>(&given_val);
        given_val.hash_input.pnym.as_mut().unwrap().context[0] ^= 0x01;
        let tracker = compile_logic::tracker::AssertionTracker::new();
        let l = EvalLogic::new_with_tracker(&f, &tracker);
        let bv = BitvecLogic::new(&l);
        let wg = evaluate_given(&l, &bv, &given_val);
        let wd = evaluate_derived(&l, &bv, &derived_val);
        let mdoc = MdocHash::with_pnym(&l, 1, true);
        let res = mdoc.assert_valid_presentation_and_macs(&wg, &wd);
        assert!(res.is_err());
        res.assert_any_failed_at(
            "assert_valid_presentation_and_macs/assert_valid_presentation/assert_pnym/assert_pnym_attribute/assert_pnym_value_and_hash/pnym_context_copy/pnym_context_copy.0/ctx_byte_imp",
        );
    }
}

#[test]
fn test_eval_mdoc_hash_4attr_pnym() {
    use mdoc_zk_circuits::hash::pnym_hash_input_of_parsed_mdoc;

    let f = Gf2_128Field::new();
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::PNYM_SEED_MDOC);
    let context = b"relying-party.example/4attr-pnym";
    let hi = pnym_hash_input_of_parsed_mdoc(
        &parsed,
        &[b"age_over_18", b"birth_date", b"age_over_18", b"birth_date"],
        context,
        now,
    );
    let mac_input = HashMac {
        mac_av: 0x112233445566778899aabbccddeeff00u128,
        mac_ap: [[0xabcdef, 0x123456]; 3],
    };
    let given_val = given::<4, _>(hi, mac_input);
    let derived_val = derived::<4, _>(&given_val);

    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    let bv = BitvecLogic::new(&l);
    let wg = evaluate_given(&l, &bv, &given_val);
    let wd = evaluate_derived(&l, &bv, &derived_val);
    let mdoc = MdocHash::with_pnym(&l, 4, true);
    mdoc.assert_valid_presentation_and_macs(&wg, &wd).unwrap();
}

#[test]
fn test_eval_mdoc_hash_2_large_190b_and_20b() {
    use mdoc_zk_circuits::cbor::mdoc::parse_mdoc;
    use sha2::{Digest, Sha256};

    let f = Gf2_128Field::new();
    let base_case = &mdoc_zk_testcases::vectors::PNYM_SEED_MDOC;
    let base = base_case.mdoc;

    // 1. 190-byte IssuerSignedItemBytes (4 SHA-256 blocks: 190 + 9 = 199 > 192 bytes):
    //    70-byte fixed CBOR framing + 11-byte cbor_id (b"\x6alarge_190b") + 109-byte cbor_value = 190 bytes.
    let mut val_109b = vec![0x58, 0x6b]; // bstr(107) -> 109 CBOR bytes
    val_109b.extend((0..107u8).map(|i| i.wrapping_mul(5).wrapping_add(3)));

    // 2. 20-byte attribute value (bstr(19) -> 20 CBOR bytes):
    let mut val_20b = vec![0x53]; // bstr(19) -> 20 CBOR bytes
    val_20b.extend((0..19u8).map(|i| i.wrapping_add(0x30)));
    assert_eq!(val_20b.len(), 20);

    let encode_item = |digest_id: u8, rand_byte: u8, attr_id: &[u8], cbor_val: &[u8]| -> Vec<u8> {
        let mut map = vec![0xa4];
        map.extend_from_slice(b"\x68digestID");
        map.push(digest_id);
        map.extend_from_slice(b"\x66random\x50");
        map.extend_from_slice(&[rand_byte; 16]);
        map.extend_from_slice(b"\x71elementIdentifier");
        map.push(0x60 + u8::try_from(attr_id.len()).unwrap());
        map.extend_from_slice(attr_id);
        map.extend_from_slice(b"\x6celementValue");
        map.extend_from_slice(cbor_val);
        let mut item = vec![0xd8, 0x18, 0x58, u8::try_from(map.len()).unwrap()];
        item.extend_from_slice(&map);
        item
    };

    let item_190b = encode_item(0, 0x42, b"large_190b", &val_109b);
    let item_20b = encode_item(1, 0x44, b"small_20b_", &val_20b);
    assert_eq!(item_190b.len(), 190);
    assert_eq!(item_20b.len(), 101);

    let ns_prefix = b"\x71org.iso.18013.5.1\x83";
    let items_start = base
        .windows(ns_prefix.len())
        .position(|w| w == ns_prefix)
        .unwrap()
        + ns_prefix.len();
    let issuer_auth_pos = base
        .windows(b"\x6aissuerAuth".len())
        .position(|w| w == b"\x6aissuerAuth")
        .unwrap();
    let item2 = &base[issuer_auth_pos - 95..issuer_auth_pos];

    let mut mdoc = base.to_vec();
    let mso_marker = [0x59, 0x01, 0xe8, 0xd8, 0x18, 0x59, 0x01, 0xe3];
    let mso_bstr_pos = mdoc
        .windows(mso_marker.len())
        .position(|w| w == mso_marker)
        .unwrap();
    let mso_wrapped_start = mso_bstr_pos + 3;
    let mso_wrapped_end = mso_wrapped_start + 0x01e8;

    let d0: [u8; 32] = Sha256::digest(&item_190b).into();
    let d1: [u8; 32] = Sha256::digest(&item_20b).into();
    let mso_slice = &mut mdoc[mso_wrapped_start..mso_wrapped_end];
    let d0_pos = mso_slice
        .windows(3)
        .position(|w| w == [0x00, 0x58, 0x20])
        .unwrap()
        + 3;
    mso_slice[d0_pos..d0_pos + 32].copy_from_slice(&d0);
    let d1_pos = mso_slice
        .windows(3)
        .position(|w| w == [0x01, 0x58, 0x20])
        .unwrap()
        + 3;
    mso_slice[d1_pos..d1_pos + 32].copy_from_slice(&d1);

    let mut new_items = Vec::new();
    new_items.extend_from_slice(&item_190b);
    new_items.extend_from_slice(&item_20b);
    new_items.extend_from_slice(item2);
    mdoc.splice(items_start..issuer_auth_pos, new_items);

    let parsed: mdoc_zk_circuits::cbor::mdoc::ParsedMdoc<CompileNat<4>> =
        parse_mdoc(&mdoc, base_case.transcript, base_case.doc_type).unwrap();
    let hi = hash_input_of_parsed_mdoc(
        &parsed,
        &[b"large_190b", b"small_20b_"],
        base_case.now,
    );
    let mac_input = HashMac {
        mac_av: 0x112233445566778899aabbccddeeff00u128,
        mac_ap: [[0xabcdef, 0x123456]; 3],
    };

    // Positive: 2-attribute large circuit (2, false) passes with 190B item + 20B value
    let given_val = given::<4, _>(hi.clone(), mac_input.clone());
    assert_eq!(given_val.attribute_given[0].unpadded_preimage_len, 190);
    assert_eq!(given_val.attribute_given[1].unpadded_preimage_len, 101);
    let derived_val = derived::<4, _>(&given_val);

    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    let bv = BitvecLogic::new(&l);
    let wg = evaluate_given(&l, &bv, &given_val);
    let wd = evaluate_derived(&l, &bv, &derived_val);
    let mdoc_hash = MdocHash::new(&l, 2);
    mdoc_hash
        .assert_valid_presentation_and_macs(&wg, &wd)
        .unwrap();

    // Negative 1: Tamper with byte 100 (> 64) of the 190-byte attribute's disclosed value
    let mut hi_bad_190b = hi.clone();
    hi_bad_190b.attrs[0].expected_cbor_value[100] ^= 0x01;
    let given_bad_190b = given::<4, _>(hi_bad_190b, mac_input.clone());
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    let bv = BitvecLogic::new(&l);
    let wg_bad_190b = evaluate_given(&l, &bv, &given_bad_190b);
    let wd_bad_190b = evaluate_derived(&l, &bv, &derived_val);
    let mdoc_hash = MdocHash::new(&l, 2);
    let res_bad_190b = mdoc_hash.assert_valid_presentation_and_macs(&wg_bad_190b, &wd_bad_190b);
    assert!(res_bad_190b.is_err());

    // Negative 2: Tamper with the 20-byte attribute's disclosed value
    let mut hi_bad_20b = hi;
    hi_bad_20b.attrs[1].expected_cbor_value[19] ^= 0x01;
    let given_bad_20b = given::<4, _>(hi_bad_20b, mac_input);
    let tracker = compile_logic::tracker::AssertionTracker::new();
    let l = EvalLogic::new_with_tracker(&f, &tracker);
    let bv = BitvecLogic::new(&l);
    let wg_bad_20b = evaluate_given(&l, &bv, &given_bad_20b);
    let wd_bad_20b = evaluate_derived(&l, &bv, &derived_val);
    let mdoc_hash = MdocHash::new(&l, 2);
    let res_bad_20b = mdoc_hash.assert_valid_presentation_and_macs(&wg_bad_20b, &wd_bad_20b);
    assert!(res_bad_20b.is_err());
}

