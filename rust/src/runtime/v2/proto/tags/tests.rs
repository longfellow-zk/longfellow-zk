// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

/// `ALL` lists its tags once each, in value order, above the terminators,
/// each with a schema, and `from_value` inverts `value` on them.
#[test]
fn tags_are_listed_once_in_value_order() {
    for pair in Tag::ALL.windows(2) {
        assert!(pair[0].value() < pair[1].value(), "{pair:?}");
    }
    for t in Tag::ALL {
        assert!(t.value() >= 16, "{t:?} collides with a terminator");
        assert_eq!(Tag::from_value(t.value()), Some(t));
        assert!(!t.schema().is_empty(), "{t:?} has no values");
    }
    let listed = (0..=u8::MAX as u64)
        .filter(|&v| Tag::from_value(v).is_some())
        .count();
    assert_eq!(listed, Tag::ALL.len());
}

/// `admits` checks the arity, the kinds and every count the schema fixes.
#[test]
fn a_schema_admits_exactly_its_values() {
    let b = Kind::Bytes.value();
    let n = Kind::Nats.value();
    assert!(Tag::Circuit.admits(&[(b, 32)]));
    assert!(!Tag::Circuit.admits(&[(b, 31)]));
    assert!(!Tag::Circuit.admits(&[(b, 32), (n, 1)]));
    assert!(!Tag::Circuit.admits(&[(n, 32)]));
    assert!(Tag::ZkStatement.admits(&[(b, 30), (b, 0)]));
    assert!(!Tag::ZkStatement.admits(&[(b, 30)]));
}
