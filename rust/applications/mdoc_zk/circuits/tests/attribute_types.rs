// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::compile::{algebra::gf2_128::Gf2_128Field, logic::eval::EvalLogic};

#[test]
fn item_slots_require_their_declared_cbor_types() {
    let f = Gf2_128Field::new();
    let tracker = crate::compile::logic::tracker::AssertionTracker::new();
    let logic = EvalLogic::new_with_tracker(&f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let verifier = AttributeVerifier::new(&logic);
    for (key, unsigned, good, bad, tail) in [
        (K_DIGEST_ID.as_slice(), true, 0x00, 0x20, vec![]),
        (K_RANDOM_ID.as_slice(), false, 0x58, 0x78, vec![0x01, 0x61]),
    ] {
        let mut raw = key.to_vec();
        raw.push(good);
        raw.extend(tail);
        let locator = FieldLocator {
            slot_position: std::array::from_fn(|_| bits.of_u64::<K_ATTR_INDEX_BITS>(0)),
            length: std::array::from_fn(|_| bits.of_u64::<K_ATTR_INDEX_BITS>(raw.len() as u64)),
            permutation: std::array::from_fn(|i| bits.of_u64::<2>(i as u64)),
        };
        let wire: Vec<_> = raw.iter().map(|&b| bits.of_u8(b)).collect();
        assert!(verifier
            .assert_item_slot_key_only(0, &locator, &wire, key, unsigned)
            .is_ok());
        raw[key.len()] = bad;
        let wire: Vec<_> = raw.iter().map(|&b| bits.of_u8(b)).collect();
        verifier
            .assert_item_slot_key_only(0, &locator, &wire, key, unsigned)
            .assert_any_failed_at("assert_item_slot_key_only/major_type");
    }
}
