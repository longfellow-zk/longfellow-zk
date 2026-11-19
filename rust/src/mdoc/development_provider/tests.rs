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
use crate::{
    core::proto::archive::CircuitArchiveBuilder,
    mdoc::proto::{NEXT_ATTRIBUTES, NEXT_VERSION},
};

pub(crate) mod fixtures;

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
}

#[test]
fn next_compilation_is_reproducible_and_unregistered() {
    // Two real compilations, never the cached circuit.
    let one = fixtures::one_compilation();
    let first = compile_next().unwrap();
    let ProvidedCircuit::V2(second) = materialize(CircuitRequest::Next).unwrap() else {
        panic!("NEXT must use v2")
    };
    drop(one);
    assert_eq!(first.spec(), second.spec());
    assert_eq!(first.compressed(), second.compressed());
    assert!(first.spec().supports_version());
    assert!(v2::find_zk_spec(v2::SYSTEM_ID, &first.spec().combined_hash).is_none());

    let mut saved = Vec::new();
    write_next(&mut saved, &first).unwrap();
    let restored = read_next(saved.as_slice()).unwrap();
    assert_eq!(restored.spec(), first.spec());
    assert_eq!(restored.compressed(), first.compressed());
    // The tests' cached circuit is the one the compiler produces.
    let cached = fixtures::next_circuit();
    assert_eq!(cached.spec(), first.spec());
    assert_eq!(cached.compressed(), first.compressed());
}

#[test]
fn next_cache_preserves_the_complete_spec() {
    use crate::{mdoc::v2::ZkSpecStruct, runtime::v2::proto::polygero::PolygeroConfig};
    let mut builder = CircuitArchiveBuilder::new();
    builder.circuit_version = Some(NEXT_VERSION as u32);
    builder.add_entry("sig", [1; 32], vec![1]);
    builder.add_entry("hash", [2; 32], vec![2]);
    let archive = builder.build();
    // Deliberately different choices from NEXT's policy: loading must not retune them.
    let spec = ZkSpecStruct {
        combined_hash: archive.combined_id,
        version: NEXT_VERSION,
        num_attributes: NEXT_ATTRIBUTES,
        polygero: PolygeroConfig {
            k: 512,
            s: 19,
            n: 3584,
            t: 90,
        },
    };
    let compressed = zstd::encode_all(archive.to_bytes().as_slice(), 1).unwrap();
    let provided = v2::provider::from_compressed(spec, compressed).unwrap();
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
    // A version-1 bundle, which stored a profile per field, is not read.
    let mut v1 = b"MDOCNEXT1".to_vec();
    v1.extend_from_slice(&spec.combined_hash);
    let p = spec.polygero;
    for value in [spec.version, spec.num_attributes, p.k, p.n, p.s, p.t] {
        v1.extend_from_slice(&(value as u64).to_le_bytes());
    }
    v1.extend_from_slice(&bytes[57..89]);
    v1.extend_from_slice(provided.compressed());
    assert!(read_next(v1.as_slice()).is_err());
}

#[test]
fn next_cache_rejects_invalid_parameter_dimensions_without_retuning() {
    use crate::runtime::v2::proto::polygero::PolygeroConfig;
    let mut builder = CircuitArchiveBuilder::new();
    builder.circuit_version = Some(NEXT_VERSION as u32);
    builder.add_entry("sig", [1; 32], vec![1]);
    builder.add_entry("hash", [2; 32], vec![2]);
    let archive = builder.build();
    // Small research/test parameters remain valid; geometry is not a certificate.
    let parameters = PolygeroConfig {
        k: 8,
        s: 0,
        n: 64,
        t: 1,
    };
    let spec = v2::ZkSpecStruct {
        combined_hash: archive.combined_id,
        version: NEXT_VERSION,
        num_attributes: NEXT_ATTRIBUTES,
        polygero: parameters,
    };
    let compressed = zstd::encode_all(archive.to_bytes().as_slice(), 1).unwrap();
    let provided = v2::provider::from_compressed(spec, compressed).unwrap();
    let mut saved = Vec::new();
    write_next(&mut saved, &provided).unwrap();
    assert_eq!(read_next(saved.as_slice()).unwrap().spec(), &spec);
    // Header: 9-byte marker, 32-byte ID, version/count, then k,n,s,t.
    for (offset, value) in [(57, 0u64), (65, 1), (73, u64::MAX), (81, 8)] {
        let mut changed = saved.clone();
        changed[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        assert!(read_next(changed.as_slice()).is_err());
    }
}
