// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use sha2::{Digest, Sha256};

use super::*;
use crate::{
    compile::{
        algebra::{gf2_128::Gf2_128Field, CompileNat},
        logic::eval::EvalLogic,
    },
    core::algebra::Nat,
    mdoc::circuits::{
        hash::{concrete, evaluate_derived, evaluate_given},
        parse_test_data,
    },
};

fn fixture() -> concrete::ConcreteGiven<CompileNat<4>> {
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&crate::mdoc::testcases::vectors::TEST_DATA);
    concrete::given::<4, _>(concrete::hash_input_of_parsed_mdoc(
        &parsed,
        &parsed.all_attr_ids(),
        now,
    ))
}

#[test]
fn doc_type_requires_the_complete_signed_length() {
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::tracker::AssertionTracker::new();
    let logic = EvalLogic::new_with_tracker(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let hash = MdocHash::new(&logic, 0);
    let mut witness = fixture();
    for expected in [b"org.iso".as_slice(), b"".as_slice()] {
        witness.hash_input.expected_doc_type = expected.to_vec();
        let wires = evaluate_given(&logic, &bits, &witness);
        hash.assert_mso_doc_type(&wires, &wires.preimage.value)
            .assert_any_failed_at("assert_mso_doc_type/text_length");
    }
}

#[test]
fn valid_until_must_end_before_sha_padding() {
    let mut witness = fixture();
    let timestamp = usize::from(witness.valid_until_offset_in_preimage) + K_VALID_UNTIL_LEN;
    witness.hash_input.cbor_mso.truncate(timestamp);
    witness.hash_input.issuer_sig_e =
        CompileNat::<4>::from_bytes_be(&Sha256::digest(&witness.hash_input.cbor_mso));
    witness = concrete::given::<4, _>(witness.hash_input);
    assert_eq!(witness.preimage.value[timestamp], 0x80);
    let derived = concrete::derived::<4, _>(&witness);
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::tracker::AssertionTracker::new();
    let logic = EvalLogic::new_with_tracker(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let wires = evaluate_given(&logic, &bits, &witness);
    let hash = MdocHash::new(&logic, witness.hash_input.attrs.len());
    assert!(
        hash.assert_mso_validity(&wires, &wires.preimage.value)
            .is_err(),
        "SHA padding is not an authenticated timestamp"
    );
    assert!(hash
        .assert_valid_presentation(&wires, &evaluate_derived(&logic, &bits, &derived))
        .is_err());
}

#[test]
fn fixed_field_reads_fit_the_entire_unpadded_range() {
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::tracker::AssertionTracker::new();
    let logic = EvalLogic::new_with_tracker(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let hash = MdocHash::new(&logic, 0);
    let preimage: Vec<_> = (0..160).map(|_| bits.of_u8(0)).collect();
    for count in [K_VALID_FROM_LEN + 20, K_VALID_UNTIL_LEN + 20, 100, 34, 13] {
        let offset = bits.of_u64::<16>(25);
        let end = bits.of_u64::<16>((25 + count) as u64);
        let short = bits.of_u64::<16>((24 + count) as u64);
        assert!(hash
            .shift_preimage(&offset, &end, 3, count, &preimage, &bits.of_u8(0))
            .1
            .is_ok());
        assert!(
            hash.shift_preimage(&offset, &short, 3, count, &preimage, &bits.of_u8(0))
                .1
                .is_err(),
            "field of {count} bytes must not read past its signed range"
        );
    }
    assert!(
        hash.shift_preimage(
            &bits.of_u64::<16>(65530),
            &bits.of_u64::<16>(65535),
            3,
            34,
            &preimage,
            &bits.of_u8(0)
        )
        .1
        .is_err(),
        "the range sum must not wrap"
    );
}

#[test]
fn every_selected_field_reports_an_out_of_message_read() {
    let witness = fixture();
    let derived = concrete::derived::<4, _>(&witness);
    let f = Gf2_128Field::new();
    for field in 0..6 {
        let tracker = crate::compile::logic::tracker::AssertionTracker::new();
        let logic = EvalLogic::new_with_tracker(&f, &tracker);
        let bits = BitvecLogic::new(&logic);
        let mut wires = evaluate_given(&logic, &bits, &witness);
        let last = bits.of_u64::<16>(u64::from(witness.preimage.len) - 1);
        let scope = match field {
            0 => {
                wires.doc_type_offset_in_preimage = last;
                "assert_mso_doc_type"
            }
            1 => {
                wires.valid_from_offset_in_preimage = last;
                "valid_from"
            }
            2 => {
                wires.valid_until_offset_in_preimage = last;
                "valid_until"
            }
            3 => {
                wires.dev_key_info_offset_in_preimage = last;
                "assert_mso_device_key"
            }
            4 => {
                wires.value_digests_offset_in_preimage = last;
                "assert_mso_value_digests"
            }
            _ => {
                wires.attribute_given[0].mso_digest_offset_in_preimage = last;
                "attribute_item"
            }
        };
        let result = MdocHash::new(&logic, witness.hash_input.attrs.len())
            .assert_valid_presentation(&wires, &evaluate_derived(&logic, &bits, &derived));
        assert!(
            result
                .failed_paths()
                .iter()
                .any(|p| p.contains(scope) && p.ends_with("shift_preimage_bounds/end")),
            "{scope} must check its entire read: {:?}",
            result.failed_paths()
        );
        assert!(!result
            .failed_paths()
            .iter()
            .any(|p| p.starts_with("assert_valid_presentation/assert_message_hash/")));
    }
}

#[test]
fn compiled_ranges_reject_crossing_and_wrapping_the_message_end() {
    use crate::{
        circuits::bitvec::BitvecIO,
        core::{algebra::AlgebraicField, proto::FieldID},
        runtime::algebra::gf2_128::Gf2_128Field as RuntimeGf128,
    };
    let fc = Gf2_128Field::new();
    let f = RuntimeGf128::new();
    let (circuit, _, symbols) = crate::compile::compiler::compile_v2(&fc, |logic| {
        let bits = BitvecLogic::new(&logic);
        let io = BitvecIO::new(&bits);
        let mut position = crate::compile::logic::K_FIRST_WIRE_POSITION;
        let offset = io.next::<16>(&mut position);
        let length = io.next::<16>(&mut position);
        let consumed = io.next::<16>(&mut position);
        (
            MdocHash::new(&logic, 0).assert_preimage_range(&offset, &length, &consumed),
            1,
        )
    });
    for (offset, length, consumed, valid) in [
        (25u16, 100u16, 75u16, true),
        (25, 99, 75, false),
        (65530, 65535, 34, false),
    ] {
        let field = &f;
        let inputs: Vec<_> = [offset, length, consumed]
            .into_iter()
            .flat_map(|value| {
                (0..16).map(move |bit| {
                    if value >> bit & 1 == 1 {
                        field.one()
                    } else {
                        field.zero()
                    }
                })
            })
            .collect();
        let result = crate::compile::eval::eval_circuit_fc(
            &fc,
            &f,
            &circuit,
            &symbols,
            &inputs,
            FieldID::Gf2_128,
        )
        .unwrap();
        if valid {
            result.assert_all_passed();
        } else {
            result.assert_any_failed_at("shift_preimage_bounds/end");
        }
    }
}

#[test]
fn signed_envelope_constraints_reject_rehashed_documents() {
    let original = fixture();
    let f = Gf2_128Field::new();
    // Keep every field's location unchanged and recompute SHA. Each failure
    // must therefore include the new envelope assertion, not a stale hash.
    for (index, path) in [
        (1, "assert_bytes_at"),
        (K_COSE1_PREFIX_LEN + 1, "outer_length"),
        (K_COSE1_PREFIX_LEN + 2, "assert_bytes_at"),
        (K_COSE1_PREFIX_LEN + 4, "assert_bytes_at"),
        (K_COSE1_PREFIX_LEN + 6, "inner_length"),
        (K_COSE1_PREFIX_LEN + 7, "map_type"),
    ] {
        let mut input = original.hash_input.clone();
        input.cbor_mso[index] ^= if path == "map_type" { 0x20 } else { 1 };
        input.issuer_sig_e = CompileNat::<4>::from_bytes_be(&Sha256::digest(&input.cbor_mso));
        let witness = concrete::given::<4, _>(input);
        let derived = concrete::derived::<4, _>(&witness);
        let tracker = crate::compile::logic::tracker::AssertionTracker::new();
        let logic = EvalLogic::new_with_tracker(&f, &tracker);
        let bits = BitvecLogic::new(&logic);
        let wires = evaluate_given(&logic, &bits, &witness);
        let derived = evaluate_derived(&logic, &bits, &derived);
        let hash = MdocHash::new(&logic, witness.hash_input.attrs.len());
        let result = hash.assert_valid_presentation(&wires, &derived);
        assert!(result.is_err());
        assert!(
            result.failed_paths().iter().any(|p| p
                .starts_with("assert_valid_presentation/assert_mso_envelope/")
                && p.contains(path)),
            "mutation at {index} must trigger {path}: {:?}",
            result.failed_paths()
        );
        assert!(
            !result
                .failed_paths()
                .iter()
                .any(|p| p.contains("assert_message_hash")),
            "the regenerated SHA witness must still pass"
        );
    }
}

#[test]
fn doc_type_checks_types_lengths_and_actual_read_end() {
    let f = Gf2_128Field::new();
    let original = fixture();
    let check = |expected: &[u8], header: &[u8], content: &[u8], suppress: bool, valid: bool| {
        let mut witness = original.clone();
        witness.hash_input.expected_doc_type = expected.to_vec();
        witness.hash_input.suppress_doc_type_check = suppress;
        let start = 25;
        let mut bytes = K_DOCTYPE_HEADER_CHECK_CBOR.to_vec();
        bytes.extend_from_slice(header);
        bytes.extend_from_slice(content);
        witness.doc_type_offset_in_preimage = start as u16;
        witness.preimage.value.fill(0);
        witness.preimage.value[start..start + bytes.len()].copy_from_slice(&bytes);
        witness.preimage.len = (start + bytes.len()) as u16;
        let tracker = crate::compile::logic::tracker::AssertionTracker::new();
        let logic = EvalLogic::new_with_tracker(&f, &tracker);
        let bits = BitvecLogic::new(&logic);
        let wires = evaluate_given(&logic, &bits, &witness);
        let result = MdocHash::new(&logic, 0).assert_mso_doc_type(&wires, &wires.preimage.value);
        assert_eq!(
            result.is_ok(),
            valid,
            "header={header:?}, expected={}, content={}, suppress={suppress}: {:?}",
            expected.len(),
            content.len(),
            result.failed_paths()
        );
        if !valid {
            assert!(result
                .failed_paths()
                .iter()
                .any(|p| p.contains("text_length")
                    || p.contains("public_length")
                    || p.contains("shift_preimage_bounds/end")));
        }
    };
    // Include short values at the very end: the unused routing window need not fit.
    for n in [1, 23, 24, 32] {
        let value = vec![b'a'; n];
        check(&value, &[0x78, n as u8], &value, false, true);
        if n < 24 {
            check(&value, &[0x60 + n as u8], &value, false, true);
        }
    }
    check(b"a", &[0x41], b"a", false, false); // byte string, not text
    check(b"a", &[0x78, 2], b"a", false, false);
    check(b"ab", &[0x61], b"ab", false, false);
    check(b"ab", &[0x62], b"a", false, false); // text extends beyond the message
    check(b"", &[0x60], b"", false, false);
    check(&[b'a'; 33], &[0x78, 33], &[b'a'; 33], false, false);
    check(b"", &[0xff], b"", true, true); // explicit suppression is preserved
}

#[test]
fn doc_type_header_type_is_checked_after_rehashing() {
    let mut input = fixture().hash_input;
    let header = K_COSE1_PREFIX_LEN + 7 + input.doc_type_offset + K_DOCTYPE_HEADER_CHECK_CBOR.len();
    input.cbor_mso[header] ^= 0x20; // text -> byte string, same length and payload
    input.issuer_sig_e = CompileNat::<4>::from_bytes_be(&Sha256::digest(&input.cbor_mso));
    let witness = concrete::given::<4, _>(input);
    let derived = concrete::derived::<4, _>(&witness);
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::tracker::AssertionTracker::new();
    let logic = EvalLogic::new_with_tracker(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let wires = evaluate_given(&logic, &bits, &witness);
    let result = MdocHash::new(&logic, witness.hash_input.attrs.len())
        .assert_valid_presentation(&wires, &evaluate_derived(&logic, &bits, &derived));
    result.assert_any_failed_at("assert_valid_presentation/assert_mso_doc_type/text_length");
    assert!(!result
        .failed_paths()
        .iter()
        .any(|p| p.contains("assert_message_hash")));
}

#[test]
fn public_attribute_lengths_must_fit_the_allocated_arrays() {
    let original = fixture();
    let derived = concrete::derived::<4, _>(&original);
    let f = Gf2_128Field::new();
    for name in [true, false] {
        let tracker = crate::compile::logic::tracker::AssertionTracker::new();
        let logic = EvalLogic::new_with_tracker(&f, &tracker);
        let bits = BitvecLogic::new(&logic);
        let mut wires = evaluate_given(&logic, &bits, &original);
        let attribute = &mut wires.disclosed_attributes[0];
        if name {
            attribute.expected_name.len = bits.of_u64::<10>(33);
        } else {
            attribute.expected_cbor_value.len = bits.of_u64::<10>(65);
        }
        let result = MdocHash::new(&logic, original.hash_input.attrs.len())
            .assert_valid_presentation(&wires, &evaluate_derived(&logic, &bits, &derived));
        assert!(
            result.failed_paths().iter().any(|p| p
                .starts_with("assert_valid_presentation/assert_attributes/")
                && p.ends_with("public_length")),
            "the capacity assertion must reject this public statement: {:?}",
            result.failed_paths()
        );
    }
}

#[test]
fn attribute_type_checks_reject_documents_with_fresh_hashes() {
    use crate::mdoc::proto::mso_attribute::constants::{K_DIGEST_ID, K_RANDOM_ID};
    let original = fixture().hash_input;
    let f = Gf2_128Field::new();
    for (slot, key_length) in [(0, K_DIGEST_ID.len()), (1, K_RANDOM_ID.len())] {
        let mut input = original.clone();
        let attribute = &mut input.attrs[0];
        let physical = (attribute.field_locator.permutation >> (2 * slot)) & 3;
        let header = attribute.field_locator.slot_position[physical] + key_length;
        attribute.cbor_issuer_signed_item[header] ^= 0x20;
        let digest = Sha256::digest(&attribute.cbor_issuer_signed_item);
        let digest_start =
            K_COSE1_PREFIX_LEN + 7 + attribute.mso_digest_offset_in_preimage + K_TAG32.len();
        input.cbor_mso[digest_start..digest_start + 32].copy_from_slice(&digest);
        input.issuer_sig_e = CompileNat::<4>::from_bytes_be(&Sha256::digest(&input.cbor_mso));
        let witness = concrete::given::<4, _>(input);
        let derived = concrete::derived::<4, _>(&witness);
        let tracker = crate::compile::logic::tracker::AssertionTracker::new();
        let logic = EvalLogic::new_with_tracker(&f, &tracker);
        let bits = BitvecLogic::new(&logic);
        let wires = evaluate_given(&logic, &bits, &witness);
        let result = MdocHash::new(&logic, witness.hash_input.attrs.len())
            .assert_valid_presentation(&wires, &evaluate_derived(&logic, &bits, &derived));
        result.assert_any_failed_at("assert_valid_presentation/assert_attributes/assert_attributes.0/attribute_item/assert_attribute/assert_item_slot_key_only/major_type");
        assert!(
            !result
                .failed_paths()
                .iter()
                .any(|p| p.contains("assert_message_hash")),
            "both the attribute and MSO SHA witnesses must still pass"
        );
    }
}

#[test]
fn sha256_matches_independent_reference_at_padding_boundaries() {
    use crate::circuits::sha256msg;
    let f = Gf2_128Field::new();
    for length in [0, 1, 55, 56, 63, 64, 119, 120, K_MSO_PREIMAGE_LEN - 9] {
        let message: Vec<_> = (0..length).map(|i| (i % 251) as u8).collect();
        let reference = Sha256::digest(&message);
        let mut given = sha256msg::given(
            &message,
            &crate::circuits::sha256::constants::INITIAL,
            K_MAX_SHA_BLOCKS,
        )
        .unwrap();
        let expected = std::array::from_fn(|i| {
            u32::from_be_bytes(reference[4 * i..4 * i + 4].try_into().unwrap())
        });
        assert_eq!(given.expected_hash, expected, "length={length}");
        given.expected_hash = expected;
        let derived = sha256msg::derived(&given, K_MAX_SHA_BLOCKS);
        let tracker = crate::compile::logic::tracker::AssertionTracker::new();
        let logic = EvalLogic::new_with_tracker(&f, &tracker);
        let bits = BitvecLogic::new(&logic);
        Sha256Msg::<_, K_MAX_SHA_BLOCKS>::new(&logic)
            .assert_message_hash(
                &sha256msg::evaluate_given::<_, 8>(&given, &bits),
                &sha256msg::evaluate_derived(&derived, &bits),
            )
            .unwrap();
    }
}

#[test]
fn raw_offsets_are_rejected_instead_of_narrowed_or_wrapped() {
    let input = fixture().hash_input;
    for offset in [u16::MAX as usize, u16::MAX as usize + 1, usize::MAX] {
        let mut invalid = input.clone();
        invalid.doc_type_offset = offset;
        assert!(std::panic::catch_unwind(|| concrete::given::<4, _>(invalid)).is_err());
        let mut invalid = input.clone();
        invalid.attrs[0].mso_digest_offset_in_preimage = offset;
        assert!(std::panic::catch_unwind(|| concrete::given::<4, _>(invalid)).is_err());
    }
}

#[test]
#[should_panic(expected = "Mismatched number of attribute witnesses")]
fn missing_attribute_witness_is_rejected_before_indexing() {
    let witness = fixture();
    let derived = concrete::derived::<4, _>(&witness);
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::tracker::AssertionTracker::new();
    let logic = EvalLogic::new_with_tracker(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let mut wires = evaluate_given(&logic, &bits, &witness);
    wires.attribute_given.pop();
    let _ = MdocHash::new(&logic, witness.hash_input.attrs.len())
        .assert_valid_presentation(&wires, &evaluate_derived(&logic, &bits, &derived));
}
