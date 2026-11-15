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
use super::limits::{SizeLimits, MAX_TOTAL_TERMS};
use crate::core::algebra::{FieldID, SerializableField};

pub struct CircuitReader<'a, F> {
    pub(super) f: &'a F,
    pub(super) field_id: FieldID,
    pub(super) limits: SizeLimits,
}

impl<'a, F: SerializableField> CircuitReader<'a, F> {
    /// The expected header field identifier comes from the field itself.
    pub fn new(f: &'a F) -> Self {
        Self {
            f,
            field_id: f.field_id(),
            limits: SizeLimits::default(),
        }
    }

    /// Lower the total expanded-term limit for this reader. The directory also
    /// enforces every fixed v2 array limit before reading circuit payloads.
    #[must_use]
    pub fn with_total_term_limit(mut self, max_total_terms: usize) -> Self {
        self.limits.expanded_terms = max_total_terms.min(MAX_TOTAL_TERMS);
        self
    }
    /// Opt into explicit size limits for a trusted compiler-produced circuit.
    ///
    /// Wire counts, stored dictionary entries, and expanded evaluation terms
    /// remain bounded independently. The ordinary reader's ceilings remain
    /// unchanged; this opt-in retains every metadata, payload, and format check.
    #[must_use]
    pub fn with_trusted_size_limits(
        mut self,
        max_total_wires: usize,
        max_total_terms: usize,
    ) -> Self {
        self.limits = SizeLimits {
            total_wires: max_total_wires,
            stored_terms: max_total_terms,
            expanded_terms: max_total_terms,
            metadata_bytes: self.limits.metadata_bytes,
        };
        self
    }
    /// Override only the decoded metadata ceiling for a trusted compiler archive.
    /// Payload bytes, circuit size limits, and every format check still apply.
    #[must_use]
    pub fn with_trusted_metadata_limit(mut self, max_metadata_bytes: usize) -> Self {
        self.limits.metadata_bytes = max_metadata_bytes;
        self
    }
}

#[cfg(test)]
mod tests;
