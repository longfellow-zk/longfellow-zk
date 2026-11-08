// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compile existing public v1 imports alongside the new canonical paths.
use std::marker::PhantomData;

use crate::runtime::{
    algebra::{p256::P256Field, SubfieldV1},
    random::{RandomEngine, Transcript},
    v1,
};

#[test]
fn legacy_runtime_paths_preserve_types_and_transcript_bytes() {
    fn same_type<T>(_: PhantomData<T>, _: PhantomData<T>) {}
    same_type(
        PhantomData::<crate::runtime::sumcheck_v1::proof::SumcheckProof<4, P256Field>>,
        PhantomData::<v1::sumcheck::proof::SumcheckProof<4, P256Field>>,
    );
    same_type(
        PhantomData::<crate::runtime::zk_v1::ZkProof<4, P256Field>>,
        PhantomData::<v1::zk::ZkProof<4, P256Field>>,
    );
    same_type(
        PhantomData::<crate::runtime::ligero_v1::LigeroProof<4, P256Field>>,
        PhantomData::<v1::ligero::LigeroProof<4, P256Field>>,
    );
    let field = P256Field::new();
    let subfield: v1::subfield::P256SubfieldV1<'_> =
        crate::runtime::algebra::p256::P256SubfieldV1::new(&field);
    assert_eq!(subfield.serialized_size_bytes(), 32);

    let mut legacy = Transcript::new(b"runtime compatibility");
    let mut canonical = v1::transcript::Transcript::new(b"runtime compatibility");
    legacy.write_bytes(b"message");
    canonical.write_bytes(b"message");
    assert_eq!(legacy.bytes(4096), canonical.bytes(4096));
}

#[test]
fn merkle_compatibility_paths_are_v1_and_v2_types_are_independent() {
    use std::any::TypeId;
    assert_eq!(
        TypeId::of::<crate::runtime::proto::Digest>(),
        TypeId::of::<v1::proto::Digest>()
    );
    assert_eq!(
        TypeId::of::<crate::runtime::proto::MerkleNonce>(),
        TypeId::of::<v1::proto::MerkleNonce>()
    );
    assert_eq!(
        TypeId::of::<crate::runtime::proto::MerkleProof>(),
        TypeId::of::<v1::proto::MerkleProof>()
    );
    assert_eq!(
        TypeId::of::<crate::runtime::merkle::MerkleHeap>(),
        TypeId::of::<v1::merkle::MerkleHeap>()
    );
    assert_eq!(
        TypeId::of::<crate::runtime::merkle::MerkleError>(),
        TypeId::of::<v1::merkle::MerkleError>()
    );
    assert_ne!(
        TypeId::of::<v1::proto::Digest>(),
        TypeId::of::<crate::runtime::v2::proto::Digest>()
    );
}
