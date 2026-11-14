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

//! Frozen v1 lookup errors and stored-archive identity.
use super::*;

#[test]
fn provider_loads_all_frozen_v1_archives() {
    assert_eq!(registered_versions_and_attrs().len(), 12);
    for expected in &ZK_SPECS {
        let provided = materialize(expected.version, expected.num_attributes).unwrap();
        assert_eq!(provided.spec, *expected);
        assert_eq!(provided.archive.combined_id, expected.combined_hash);
        assert_eq!(
            provided.compressed,
            crate::mdoc::artifacts::load_circuit_lfa2(&provided.name)
        );
    }
}

#[test]
fn provider_never_compiles_unknown_or_missing_v1_circuits() {
    let missing = Path::new(env!("CARGO_MANIFEST_DIR")).join("does-not-exist");
    assert!(matches!(
        materialize_from(&missing, 8, 1),
        Err(MdocProverErrorCode::InvalidZkSpecVersion)
    ));
    let spec = &ZK_SPECS[0];
    assert!(matches!(
        materialize_from(&missing, spec.version, spec.num_attributes),
        Err(MdocProverErrorCode::GeneralFailure)
    ));
}
