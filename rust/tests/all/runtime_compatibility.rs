// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compile existing public v1 imports alongside the new canonical paths.
use crate::runtime::{
    algebra::{p256::P256Field, SubfieldV1},
    random::{RandomEngine, Transcript},
    v1,
};
use std::marker::PhantomData;

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
