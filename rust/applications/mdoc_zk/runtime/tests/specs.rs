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

//! Frozen registry discovery and explicit v2 execution specifications.
use crate::mdoc::runtime::{v1, v2, zk_spec::*};
#[test]
fn systems_own_disjoint_specifications() {
    for spec in &v1::ZK_SPECS {
        assert!(spec.is_valid());
        assert!(
            matches!(find_zk_spec(v1::SYSTEM_ID,&spec.combined_hash),Some(ZkSpecRef::V1(found)) if found==spec)
        );
        assert!(find_zk_spec(v2::SYSTEM_ID, &spec.combined_hash).is_none());
    }
    assert!(v2::ZK_SPECS.is_empty());
    let spec = v2_spec();
    assert!(spec.supports_version()); // Execution support is independent of publication.
    assert!(find_zk_spec(v2::SYSTEM_ID, &spec.combined_hash).is_none());
    assert!(find_zk_spec_by_hex(v2::SYSTEM_ID, &spec.combined_hash_hex()).is_none());
    assert!((5..=7).all(v1::is_supported_version));
    assert!(!v1::is_supported_version(8));
    assert!(!v2::is_supported_version(7));
    assert!(!v2::is_supported_version(8));
    assert!(!v2::is_supported_version(99));
}
#[test]
fn v1_registry_matches_original_records_exactly() {
    use sha2::{Digest, Sha256};
    let mut hash = Sha256::new();
    for spec in &v1::ZK_SPECS {
        hash.update(spec.system.as_bytes());
        hash.update([0]);
        hash.update(spec.combined_hash);
        let h = spec.ligero_hash;
        let s = spec.ligero_sig;
        for n in [
            spec.num_attributes,
            spec.version,
            h.rateinv,
            h.nreq,
            h.block_enc,
            s.rateinv,
            s.nreq,
            s.block_enc,
        ] {
            hash.update((n as u64).to_le_bytes());
        }
    }
    assert_eq!(
        hash.finalize().as_slice(),
        &[
            30, 240, 120, 49, 188, 178, 233, 53, 219, 18, 123, 223, 164, 88, 127, 34, 136, 202,
            178, 65, 112, 78, 116, 103, 104, 235, 3, 94, 125, 36, 109, 214
        ]
    );
}
#[test]
fn v2_conversion_preserves_k_dimension_and_s_degree() {
    let (hash, sig) = v2_spec().configs();
    assert_eq!((hash.k, hash.n, hash.s, hash.t), (512, 3584, 18, 87));
    assert_eq!((sig.k, sig.n, sig.s, sig.t), (416, 2912, 15, 86));
}
#[test]
fn each_entry_point_rejects_unsupported_circuit_versions() {
    let mut legacy = v1::ZK_SPECS[0];
    legacy.version = 8;
    let mut next = v2_spec();
    next.version = 8;
    assert_eq!(
        v1::run_mdoc_prover_inner(
            &legacy,
            &[],
            &[],
            "",
            "",
            &[],
            &[],
            "",
            "",
            &mut crate::runtime::random::DeterministicRng::new(42)
        ),
        Err(v1::MdocProverErrorCode::InvalidZkSpecVersion)
    );
    assert_eq!(
        v2::run_mdoc_prover_inner(
            &next,
            &[],
            &[],
            "",
            "",
            &[],
            &[],
            "",
            "",
            &mut crate::runtime::random::DeterministicRng::new(42)
        ),
        Err(v2::MdocProverErrorCode::InvalidZkSpecVersion)
    );
    assert_eq!(
        v1::run_mdoc_verifier(&legacy, &[], "", "", &[], &[], "", "", &[]),
        Err(v1::MdocVerifierErrorCode::InvalidZkSpecVersion)
    );
    assert_eq!(
        v2::run_mdoc_verifier(&next, &[], "", "", &[], &[], "", "", &[]),
        Err(v2::MdocVerifierErrorCode::InvalidZkSpecVersion)
    );
}

/// Explicit development-shaped fixture; it is deliberately absent from the frozen registry.
pub(super) fn v2_spec() -> v2::ZkSpecStruct {
    v2::ZkSpecStruct {
        combined_hash: [0; 32],
        num_attributes: 1,
        version: 9,
        manifest: crate::mdoc::proto::packed::HashInputManifest {
            public_bits: 1,
            private_bits: 0,
        },
        polygero_hash: v2::PolygeroParameters {
            k: 512,
            n: 3584,
            s: 18,
            t: 87,
        },
        polygero_sig: v2::PolygeroParameters {
            k: 416,
            n: 2912,
            s: 15,
            t: 86,
        },
    }
}
