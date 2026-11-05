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

//! Native v2 LFC3 serialization.

mod lfc3;
use super::Circuit;
use crate::core::proto::{FieldID, SerializableField};

pub struct CircuitWriter<'a, F> {
    pub(super) f: &'a F,
    pub(super) field_id: FieldID,
}
impl<'a, F: SerializableField> CircuitWriter<'a, F> {
    pub fn new(f: &'a F, field_id: FieldID) -> Self {
        Self { f, field_id }
    }
    #[must_use]
    pub fn to_bytes(&self, circuit: &Circuit<F>) -> Vec<u8> {
        lfc3::to_bytes(self, circuit)
    }
}
