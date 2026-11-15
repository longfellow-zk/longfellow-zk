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

/// `ALL` holds each tag at its `index`, so it lists no tag twice, and it
/// lists every tag: `every` names each variant once, beside an exhaustive
/// match that does not compile until a new tag is named in it too.
#[test]
fn all_holds_every_tag_at_its_index() {
    for (i, t) in Tag::ALL.into_iter().enumerate() {
        assert_eq!(t.index(), i, "{t:?}");
    }
    let named = |t: Tag| match t {
        Tag::MdocStatement
        | Tag::ZkStatement
        | Tag::Circuit
        | Tag::CommitmentLayout
        | Tag::JointGeometry
        | Tag::PublicInputs
        | Tag::AdapterLayout
        | Tag::Commitment
        | Tag::FingerprintResponse
        | Tag::SumcheckRound
        | Tag::SumcheckCross
        | Tag::SumcheckClaims
        | Tag::SplitOpening
        | Tag::P256AdapterQuotients
        | Tag::PackingU
        | Tag::PackingA
        | Tag::PolygeroResponse
        | Tag::Seal => t,
    };
    let every = [
        Tag::MdocStatement,
        Tag::ZkStatement,
        Tag::Circuit,
        Tag::CommitmentLayout,
        Tag::JointGeometry,
        Tag::PublicInputs,
        Tag::AdapterLayout,
        Tag::Commitment,
        Tag::FingerprintResponse,
        Tag::SumcheckRound,
        Tag::SumcheckCross,
        Tag::SumcheckClaims,
        Tag::SplitOpening,
        Tag::P256AdapterQuotients,
        Tag::PackingU,
        Tag::PackingA,
        Tag::PolygeroResponse,
        Tag::Seal,
    ]
    .map(named);
    assert_eq!(every.len(), Tag::ALL.len());
    for t in every {
        assert!(t.index() < Tag::ALL.len(), "{t:?} is past the end of ALL");
        assert_eq!(Tag::ALL[t.index()], t, "{t:?} is not at its index");
    }
}

/// The setup tags are exactly the statement's, 16 to 31 (transcript I1).
#[test]
fn setup_tags_are_the_statement_range() {
    for t in Tag::ALL {
        assert_eq!(t.is_setup(), (16..32).contains(&t.value()), "{t:?}");
    }
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
