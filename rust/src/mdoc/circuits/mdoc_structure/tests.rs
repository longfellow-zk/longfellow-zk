// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    circuits::bitvec::BitvecLogic,
    compile::{
        algebra::{gf2_128::Gf2_128Field, CompileNat},
        logic::{AssertionScope, EvalLogic},
    },
    mdoc::{
        cbor::test_utils::parse_test_data,
        circuits::hash::{evaluate_given, given, hash_input_of_parsed_mdoc, MdocHash},
        proto::hash::constants::{K_MSO_MAX_BYTES, K_MSO_OFFSET},
        testcases::TEST_DATA,
    },
};

#[test]
fn structural_claims_reject_wrong_parents_ids_and_counter_witnesses() {
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let concrete = given::<4, _>(hash_input_of_parsed_mdoc(
        &parsed,
        &parsed.all_attr_ids(),
        now,
    ));
    let field = Gf2_128Field::new();
    for case in 0..8 {
        let tracker = AssertionScope::new();
        let logic = EvalLogic::new(&field, &tracker);
        let bv = BitvecLogic::new(&logic);
        let mut wires = evaluate_given(&logic, &bv, &concrete);
        match case {
            0 => {}
            1 => {
                wires.structure.as_mut().unwrap().digest_keys[0] =
                    wires.structure.as_ref().unwrap().digest_keys[1].clone()
            }
            2 => wires.structure.as_mut().unwrap().namespace.start = bv.of_u64(0),
            3 => wires.structure.as_mut().unwrap().validity_key = bv.of_u64(0),
            4 => {
                *wires.structure.as_mut().unwrap().maps[3]
                    .threshold
                    .last_mut()
                    .unwrap() = bv.of_u64(1)
            }
            5 => {
                wires.structure.as_mut().unwrap().attributes[0]
                    .map
                    .threshold[127] = bv.of_u64(1)
            }
            6 => wires.doc_type_offset_in_preimage = wires.dev_key_info_offset_in_preimage.clone(),
            7 => {
                // Change the decoded IssuerSignedItem ID while preserving its
                // encoding width and all its structural boundaries.
                let attr = &concrete.attribute_given[0];
                let physical = attr.field_locator.permutation & 3;
                let offset = attr.field_locator.slot_position[physical] + 9;
                wires.attribute_given[0].preimage.data[offset] =
                    bv.of_u8(attr.padded_preimage[offset] ^ 1);
            }
            _ => unreachable!(),
        }
        let checks = MdocHash::new(&logic).assert_structure(&wires);
        assert_eq!(
            checks.is_ok(),
            case == 0,
            "case {case}: {:?}",
            checks.failed_paths()
        );
    }
}

#[test]
fn exact_capacity_credential_and_one_byte_overflow() {
    use crate::mdoc::{
        cbor::{
            mdoc::{parse_mdoc, MdocParseError},
            test_utils::with_mso_size,
        },
        testcases::TEST_DATA,
    };
    let capacity = K_MSO_MAX_BYTES;
    let (bytes, _) = with_mso_size(TEST_DATA.mdoc, capacity).unwrap();
    let parsed =
        parse_mdoc::<CompileNat<4>>(&bytes, TEST_DATA.transcript, TEST_DATA.doc_type).unwrap();
    assert_eq!(parsed.cbor_mso.len() - K_MSO_OFFSET, capacity);
    let given = given::<4, _>(hash_input_of_parsed_mdoc(
        &parsed,
        &[parsed.attrs[0].name.as_slice()],
        TEST_DATA.now,
    ));
    let field = Gf2_128Field::new();
    let tracker = AssertionScope::new();
    let logic = EvalLogic::new(&field, &tracker);
    let bv = BitvecLogic::new(&logic);
    let mut wires = evaluate_given(&logic, &bv, &given);
    MdocHash::new(&logic)
        .assert_structure(&wires)
        .assert_all_passed();
    wires.preimage.len = bv.of_u64(u64::from(given.preimage.len) + 1);
    MdocHash::new(&logic)
        .assert_structure(&wires)
        .assert_any_failed_at("mdoc_structure/mso_capacity");
    let (oversized, _) = with_mso_size(TEST_DATA.mdoc, capacity + 1).unwrap();
    assert!(matches!(
        parse_mdoc::<CompileNat<4>>(&oversized, TEST_DATA.transcript, TEST_DATA.doc_type),
        Err(MdocParseError::TooBig)
    ));
}
