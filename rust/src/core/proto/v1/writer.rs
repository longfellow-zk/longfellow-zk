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

//! V1-only LFC1/LFC2 serialization.

mod lfc1;
mod lfc2;
use crate::core::algebra::{FieldID, SerializableField};

pub struct CircuitWriter<'a, F> {
    f: &'a F,
    pub(super) field_id: FieldID,
}

impl<'a, F: SerializableField> CircuitWriter<'a, F> {
    pub fn new(f: &'a F, field_id: FieldID) -> Self {
        Self { f, field_id }
    }

    pub(super) fn serialize_elt(&self, bytes: &mut Vec<u8>, v: &F::E) {
        let elt_bytes = self.f.to_bytes(v);
        bytes.extend_from_slice(&elt_bytes);
    }
}
