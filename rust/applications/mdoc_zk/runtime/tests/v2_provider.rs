// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Frozen v2 lookup and loading, including a synthetic unpublished fixture.
use super::*;
use crate::core::proto::archive::CircuitArchiveBuilder;

#[test]
fn next_is_not_a_frozen_v2_circuit() {
    assert!(registered_versions_and_attrs().is_empty());
    for count in 1..=4 {
        assert!(matches!(
            materialize(crate::mdoc::circuits::NEXT_VERSION, count),
            Err(MdocProverErrorCode::InvalidZkSpecVersion)
        ));
    }
}

#[test]
fn provider_rejects_wrong_archive_entries() {
    for names in [
        vec!["sig"],
        vec!["sig", "other"],
        vec!["sig", "hash", "extra"],
    ] {
        let mut builder = CircuitArchiveBuilder::new();
        builder.set_circuit_version(crate::mdoc::circuits::NEXT_VERSION as u32);
        for name in names {
            builder.add_entry(name, [1; 32], vec![1]);
        }
        let archive = builder.build();
        let mut spec = crate::mdoc::runtime::tests_specs::v2_spec();
        spec.combined_hash = archive.combined_id;
        let compressed = zstd::encode_all(archive.to_bytes().as_slice(), 1).unwrap();
        assert!(matches!(
            from_compressed(spec, compressed),
            Err(MdocProverErrorCode::CircuitParsingFailure)
        ));
    }
}

#[test]
fn frozen_v2_loader_reads_archive_without_a_compiler() {
    let mut builder = CircuitArchiveBuilder::new();
    builder.set_circuit_version(crate::mdoc::circuits::NEXT_VERSION as u32);
    builder.add_entry("sig", [1; 32], vec![1]);
    builder.add_entry("hash", [2; 32], vec![2]);
    let archive = builder.build();
    let mut spec = crate::mdoc::runtime::tests_specs::v2_spec();
    spec.combined_hash = archive.combined_id;
    let compressed = zstd::encode_all(archive.to_bytes().as_slice(), 1).unwrap();
    let directory =
        std::env::temp_dir().join(format!("longfellow-v2-provider-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lfa2", spec.combined_hash_hex()));
    std::fs::write(&path, &compressed).unwrap();
    // Exercise the exact loader used after registry selection without publishing a fixture.
    let provided = load(&directory, &spec).unwrap();
    assert_eq!(provided.spec(), &spec);
    assert_eq!(provided.compressed(), compressed);
    std::fs::remove_file(&path).unwrap();
    assert!(load(&directory, &spec).is_err());
    std::fs::remove_dir(directory).unwrap();
    spec.version = 99;
    assert!(from_compressed(spec, compressed.clone()).is_err());
    spec.version = crate::mdoc::circuits::NEXT_VERSION;
    spec.combined_hash[0] ^= 1;
    assert!(from_compressed(spec, compressed).is_err());
}
