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

//! V2 scalar output.

use crate::core::algebra::{ElementOf, SerializableField};

/// Helper to serialize and write a single field element.
pub(super) fn write_elt_field<F: SerializableField>(bytes: &mut Vec<u8>, e: &ElementOf<F>, f: &F) {
    let len = f.serialized_size_bytes();
    let start = bytes.len();
    bytes.resize(start + len, 0);
    f.to_bytes_into(e, &mut bytes[start..]);
}
