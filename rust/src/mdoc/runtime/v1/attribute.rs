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

//! Longfellow v1 application attribute.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestedAttribute {
    pub namespace_id: Vec<u8>,
    pub id: Vec<u8>,
    pub cbor_value: Vec<u8>,
}

pub fn req_attr(
    namespace: impl AsRef<[u8]>,
    id: impl AsRef<[u8]>,
    cbor_val: impl AsRef<[u8]>,
) -> RequestedAttribute {
    RequestedAttribute {
        namespace_id: namespace.as_ref().to_vec(),
        id: id.as_ref().to_vec(),
        cbor_value: cbor_val.as_ref().to_vec(),
    }
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[must_use]
pub(super) fn same_namespace(attrs: &[RequestedAttribute]) -> bool {
    if attrs.is_empty() {
        return true;
    }
    let ns = &attrs[0].namespace_id;
    attrs.iter().all(|a| a.namespace_id == *ns)
}
