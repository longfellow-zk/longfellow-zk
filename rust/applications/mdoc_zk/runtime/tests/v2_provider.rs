// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
#[test]
fn next_is_not_a_published_circuit() {
    assert!(registered_versions_and_attrs().is_empty());
    for version in [8, 9] {
        for count in 1..=4 {
            assert!(materialize(version, count).is_err());
        }
    }
}
#[test]
fn provider_rejects_wrong_archive_entries() {
    for names in [
        vec!["sig"],
        vec!["sig", "other"],
        vec!["sig", "hash", "extra"],
    ] {
        let mut b = crate::core::proto::archive::CircuitArchiveBuilder::new();
        b.set_circuit_version(9);
        for name in names {
            b.add_entry(name, [1; 32], vec![1]);
        }
        let a = b.build();
        let mut spec = crate::mdoc::runtime::tests_specs::v2_spec();
        spec.combined_hash = a.combined_id;
        let compressed = zstd::encode_all(a.to_bytes().as_slice(), 1).unwrap();
        assert!(from_compressed(spec, compressed).is_err());
    }
}
