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

//! Native v2 LFC3 parsing.

mod lfc3;
use super::Circuit;
use crate::core::proto::{reader::*, FieldID, SerializableField};

pub struct CircuitReader<'a, F> {
    pub(super) f: &'a F,
    pub(super) field_id: FieldID,
    pub(super) max_total_terms: usize,
}

impl<'a, F: SerializableField> CircuitReader<'a, F> {
    pub fn new(f: &'a F, field_id: FieldID) -> Self {
        Self {
            f,
            field_id,
            max_total_terms: crate::core::proto::reader::MAX_TOTAL_TERMS,
        }
    }

    /// Override the total expanded term budget for this reader. The default is
    /// 20 million. Raising this limit increases the work allowed for a circuit;
    /// use a larger budget only for trusted inputs or with an appropriate
    /// external resource limit. All other reader limits remain in effect.
    #[must_use]
    pub fn with_total_term_limit(mut self, max_total_terms: usize) -> Self {
        self.max_total_terms = max_total_terms;
        self
    }

    pub fn from_bytes<'b>(
        &self,
        bytes: &'b [u8],
        enforce_circuit_id: bool,
    ) -> Result<(Circuit<F>, &'b [u8]), String> {
        let mut cursor = bytes;
        let circuit = self.from_stream(&mut cursor, enforce_circuit_id)?;
        Ok((circuit, cursor))
    }
    pub fn from_stream<R: std::io::BufRead>(
        &self,
        stream: &mut R,
        enforce_circuit_id: bool,
    ) -> Result<Circuit<F>, String> {
        lfc3::from_stream(self, stream, enforce_circuit_id)
    }
}
#[cfg(test)]
#[path = "../../../tests/reader.rs"]
mod tests;
