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

//! Development selection and cache round trips are independent of frozen publication.
use super::*;

#[test]
fn frozen_requests_delegate_and_never_compile_next() {
    let provided = materialize(CircuitRequest::FrozenV1 {
        version: 7,
        num_attributes: 1,
    })
    .unwrap();
    let ProvidedCircuit::V1(provided) = provided else {
        panic!("wrong system")
    };
    assert_eq!(provided.spec, v1::ZK_SPECS[0]);
    assert!(materialize(CircuitRequest::FrozenV2 {
        version: 8,
        num_attributes: 1
    })
    .is_err());
    for count in [0, 5, usize::MAX] {
        assert!(materialize(CircuitRequest::Next {
            num_attributes: count
        })
        .is_err());
    }
}

#[test]
fn next_compilation_is_reproducible_and_unregistered() {
    let first = compile_next(1).unwrap();
    let second = compile_next(1).unwrap();
    assert_eq!(first.spec(), second.spec());
    assert_eq!(first.compressed(), second.compressed());
    assert!(first.spec().supports_version());
    assert!(v2::find_zk_spec(v2::SYSTEM_ID, &first.spec().combined_hash).is_none());

    let mut saved = Vec::new();
    write_next(&mut saved, &first).unwrap();
    let restored = read_next(saved.as_slice()).unwrap();
    assert_eq!(restored.spec(), first.spec());
    assert_eq!(restored.compressed(), first.compressed());
}

#[test]
fn next_cache_preserves_the_complete_spec() {
    let original = compile_next(3).unwrap();
    let mut spec = *original.spec();
    spec.polygero_hash.s += 1;
    let provided = v2::provider::from_compressed(spec, original.compressed().to_vec()).unwrap();
    let mut bytes = Vec::new();
    write_next(&mut bytes, &provided).unwrap();
    let restored = read_next(bytes.as_slice()).unwrap();
    assert_eq!(restored.spec(), &spec);
    assert_eq!(restored.compressed(), provided.compressed());
    assert!(v2::find_zk_spec(v2::SYSTEM_ID, &spec.combined_hash).is_none());
    for length in [0, 8, 40, 120, bytes.len() - 1] {
        assert!(read_next(&bytes[..length]).is_err());
    }
    let mut wrong = bytes.clone();
    wrong[9] ^= 1; // Saved circuit identifier disagrees with the archive.
    assert!(read_next(wrong.as_slice()).is_err());
    wrong = bytes.clone();
    wrong[41..49].copy_from_slice(&7u64.to_le_bytes());
    assert!(read_next(wrong.as_slice()).is_err());
    let mut legacy = spec.combined_hash.to_vec();
    legacy.extend_from_slice(provided.compressed());
    assert!(read_next(legacy.as_slice()).is_err());
}
