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
        wires.structure = Some(super::Witness::constant(&logic, &concrete.structure));
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
    wires.structure = Some(super::Witness::constant(&logic, &given.structure));
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

#[test]
fn disabled_slots_skip_all_attribute_structure_assertions() {
    use crate::{
        circuits::boolean::Boolean,
        mdoc::{cbor::structure_prover::ConcreteWitness, circuits::mdoc_structure::Witness},
    };
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let mut input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);
    input.attrs = input.attrs.iter().cycle().take(4).cloned().collect();
    let concrete = given::<4, _>(input);
    let slots = concrete
        .hash_input
        .attrs
        .iter()
        .enumerate()
        .map(|(slot, attr)| {
            (slot % 2 == 0).then_some((
                attr.mso_digest_offset_in_preimage,
                attr.cbor_issuer_signed_item.as_slice(),
            ))
        })
        .collect::<Vec<_>>();
    let witness = ConcreteWitness::derive_slots(
        &concrete.hash_input.cbor_mso,
        concrete.hash_input.namespace_offset,
        &slots,
    )
    .unwrap();
    let field = Gf2_128Field::new();
    for enabled in [false, true] {
        let tracker = AssertionScope::new();
        let logic = EvalLogic::new(&field, &tracker);
        let bits = BitvecLogic::new(&logic);
        let boolean = Boolean::new(&logic);
        let mut wires = evaluate_given(&logic, &bits, &concrete);
        wires.structure = Some(Witness::constant(&logic, &witness));
        for slot in [1, 3] {
            wires.disclosed_attributes[slot].enabled = boolean.konst(enabled);
            let attr = &mut wires.attribute_given[slot];
            attr.mso_digest_offset_in_preimage = bits.of_u64(u16::MAX.into());
            attr.preimage.len = bits.of_u64(1023);
            attr.field_locator.slot_position = std::array::from_fn(|_| bits.of_u64(1023));
            attr.field_locator.length = std::array::from_fn(|_| bits.of_u64(1023));
        }
        assert_eq!(
            MdocHash::new(&logic).assert_structure(&wires).is_ok(),
            !enabled
        );
    }
}

#[test]
fn structural_witness_preserves_disabled_slots_and_large_equality_items() {
    use crate::mdoc::{
        cbor::{
            parse::{CborParser, CborValue},
            structure_prover::ConcreteWitness,
        },
        proto::{
            hash::constants::K_STRUCTURE_ATTR_CAPACITY,
            mso_attribute::constants::K_MAX_ATTR_CBOR_LEN,
        },
    };
    let (_, parsed, _) = parse_test_data::<4, CompileNat<4>>(&TEST_DATA);
    let attr = &parsed.attrs[0];
    let original = &attr.cbor_issuer_signed_item;
    let map = CborParser::new(&original[4..]).parse_exact().unwrap();
    let CborValue::Map(entries) = map.value else {
        panic!("issuer item map");
    };
    let value = &entries
        .iter()
        .find(|(key, _)| matches!(&key.value, CborValue::Text(name) if name == "elementValue"))
        .unwrap()
        .1;
    let start = 4 + value.start;
    let end = 4 + value.end;
    let payload_len = K_MAX_ATTR_CBOR_LEN - (original.len() - (end - start)) - 2;
    let mut large = original[..start].to_vec();
    large.extend([0x58, u8::try_from(payload_len).unwrap()]);
    large.resize(large.len() + payload_len, 0);
    large.extend_from_slice(&original[end..]);
    large[3] = u8::try_from(large.len() - 4).unwrap();
    assert_eq!(large.len(), K_MAX_ATTR_CBOR_LEN);
    let namespace = parsed.namespaces().unwrap().remove(0);
    let witness = ConcreteWitness::derive_slots(
        &parsed.cbor_mso,
        namespace.key_offset,
        &[
            None,
            Some((attr.mso_digest_offset_in_preimage, &large)),
            None,
            None,
        ],
    )
    .unwrap();
    assert_eq!(witness.digest_keys.len(), 4);
    assert_eq!(witness.attributes.len(), 4);
    assert_eq!(witness.digest_keys[0], 0);
    assert_eq!(witness.digest_keys[2], 0);
    assert_eq!(witness.digest_keys[3], 0);
    assert!(witness.attributes[0]
        .lexer
        .remaining
        .iter()
        .all(|&n| n == 0));
    assert_eq!(
        witness.attributes[1].lexer.remaining.len(),
        K_STRUCTURE_ATTR_CAPACITY
    );
}
