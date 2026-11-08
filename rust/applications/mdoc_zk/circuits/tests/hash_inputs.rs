// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Namespace byte binding and chronological comparisons without separator case.
use super::*;
use crate::{
    compile::{
        algebra::{gf2_128::Gf2_128Field, CompileNat},
        logic::eval::EvalLogic,
    },
    mdoc::circuits::hash::{concrete, evaluate_derived, evaluate_given},
};

fn fixture() -> concrete::ConcreteGiven<CompileNat<4>> {
    let (_, parsed, now) = crate::mdoc::circuits::parse_test_data::<4, CompileNat<4>>(
        &crate::mdoc::testcases::vectors::TEST_DATA,
    );
    concrete::given::<4, _>(concrete::hash_input_of_parsed_mdoc(
        &parsed,
        &parsed.all_attr_ids(),
        now,
    ))
}

fn namespace_passes(expected: &[u8], encoded: &[u8], offset: u16, message_len: u16) -> bool {
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::scope::AssertionScope::new();
    let logic = EvalLogic::new(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let witness = fixture();
    let mut wires = evaluate_given(&logic, &bits, &witness);
    wires.expected_namespace.data =
        std::array::from_fn(|i| bits.of_u8(*expected.get(i).unwrap_or(&0)));
    wires.expected_namespace.len = bits.of_u64(expected.len() as u64);
    wires.namespace_offset_in_preimage = bits.of_u64(u64::from(offset));
    wires.preimage.len = bits.of_u64(u64::from(message_len));
    let preimage: Vec<_> = (0..K_MSO_PREIMAGE_LEN)
        .map(|i| {
            bits.of_u8(
                i.checked_sub(usize::from(offset))
                    .and_then(|j| encoded.get(j))
                    .copied()
                    .unwrap_or(0),
            )
        })
        .collect();
    MdocHash::new(&logic, 0)
        .assert_mso_namespace(&wires, &preimage)
        .is_ok()
}

#[test]
fn namespace_checks_exact_text_headers_lengths_and_read_bounds() {
    for len in [1, 17, 23, 24, 32, K_NAMESPACE_BYTES] {
        let namespace = vec![b'n'; len];
        let encoded = crate::mdoc::circuits::cbor::encode_cbor_string(&namespace);
        let end = 25 + encoded.len() as u16;
        assert!(namespace_passes(&namespace, &encoded, 25, end));
        let mut different = namespace.clone();
        different[len - 1] ^= 1;
        assert!(!namespace_passes(&different, &encoded, 25, end));
        assert!(!namespace_passes(&namespace[..len - 1], &encoded, 25, end));
        assert!(!namespace_passes(&namespace, &encoded, 25, end - 1));
        let mut bytes_header = encoded.clone();
        bytes_header[0] -= 0x20; // Same length, but a byte string instead of text.
        assert!(!namespace_passes(&namespace, &bytes_header, 25, end));
    }
    for len in [0, K_NAMESPACE_BYTES + 1] {
        let namespace = vec![b'n'; len];
        let encoded = crate::mdoc::circuits::cbor::encode_cbor_string(&namespace);
        assert!(!namespace_passes(&namespace, &encoded, 25, 200));
    }
    assert!(!namespace_passes(
        b"namespace",
        b"\x69namespace",
        65530,
        65535
    ));
}

#[test]
fn namespace_check_is_independent_of_doc_type_suppression() {
    let mut witness = fixture();
    witness.hash_input.suppress_doc_type_check = true;
    witness.hash_input.expected_namespace[0] ^= 1;
    let derived = concrete::derived::<4, _>(&witness);
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::scope::AssertionScope::new();
    let logic = EvalLogic::new(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    MdocHash::new(&logic, witness.hash_input.attrs.len())
        .assert_valid_presentation(
            &evaluate_given(&logic, &bits, &witness),
            &evaluate_derived(&logic, &bits, &derived),
        )
        .assert_any_failed_at(
            "assert_valid_presentation/assert_mso_namespace/value_bytes/value_bytes.0/text_byte",
        );
}

fn validity_passes(from: &[u8; 20], until: &[u8; 20], now: &[u8; 20]) -> bool {
    let mut witness = fixture();
    let from_start = usize::from(witness.valid_from_offset_in_preimage) + K_VALID_FROM_LEN;
    let until_start = usize::from(witness.valid_until_offset_in_preimage) + K_VALID_UNTIL_LEN;
    witness.preimage.value[from_start..from_start + 20].copy_from_slice(from);
    witness.preimage.value[until_start..until_start + 20].copy_from_slice(until);
    witness.hash_input.now = now.to_vec();
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::scope::AssertionScope::new();
    let logic = EvalLogic::new(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let wires = evaluate_given(&logic, &bits, &witness);
    MdocHash::new(&logic, 0)
        .assert_mso_validity(&wires, &wires.preimage.value)
        .is_ok()
}

#[test]
fn timestamp_separator_case_does_not_change_inclusive_boundaries() {
    for mask in 0..64 {
        let mut times = [*b"2024-01-01T00:00:00Z"; 3];
        for (i, timestamp) in times.iter_mut().enumerate() {
            if mask >> (2 * i) & 1 != 0 {
                timestamp[10] = b't';
            }
            if mask >> (2 * i + 1) & 1 != 0 {
                timestamp[19] = b'z';
            }
        }
        assert!(
            validity_passes(&times[0], &times[1], &times[2]),
            "case mask={mask}"
        );
    }
    for (from, until, now, valid) in [
        (
            b"2024-01-01T00:00:00Z",
            b"2024-01-01t00:00:00z",
            b"2024-01-01T12:00:00Z",
            false,
        ),
        (
            b"2024-01-01t12:00:00z",
            b"2025-01-01T00:00:00Z",
            b"2024-01-01T00:00:00Z",
            false,
        ),
        (
            b"2023-12-31T23:59:59Z",
            b"2024-02-01T00:00:00Z",
            b"2024-01-01t00:00:00z",
            true,
        ),
        (
            b"2024-02-01T00:00:00Z",
            b"2024-03-01T00:00:00Z",
            b"2024-01-31T23:59:59Z",
            false,
        ),
        (
            b"2024-01-01T00:00:00Z",
            b"2024-01-01T00:00:01Z",
            b"2024-01-01T00:00:02Z",
            false,
        ),
    ] {
        assert_eq!(validity_passes(from, until, now), valid);
    }
}

#[test]
fn every_disclosed_attribute_checks_its_last_public_bytes() {
    let f = Gf2_128Field::new();
    let original = fixture();
    let derived = concrete::derived::<4, _>(&original);
    for index in 0..original.hash_input.attrs.len() {
        for change_name in [false, true] {
            let mut changed = original.clone();
            let attribute = &mut changed.hash_input.attrs[index];
            let public = if change_name {
                &mut attribute.expected_name
            } else {
                &mut attribute.expected_cbor_value
            };
            *public.last_mut().unwrap() ^= 1;
            let tracker = crate::compile::logic::scope::AssertionScope::new();
            let logic = EvalLogic::new(&f, &tracker);
            let bits = BitvecLogic::new(&logic);
            let wires = evaluate_given(&logic, &bits, &changed);
            assert!(
                MdocHash::new(&logic, changed.hash_input.attrs.len())
                    .assert_attributes(
                        &wires,
                        &evaluate_derived(&logic, &bits, &derived),
                        &wires.preimage.value,
                    )
                    .is_err(),
                "last byte unchecked: attribute={index}, name={change_name}"
            );
        }
    }
}
