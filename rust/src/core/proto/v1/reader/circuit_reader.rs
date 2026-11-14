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

//! V1 reader state and the limits shared by the LFC1 and LFC2 parsers.

use crate::core::{
    algebra::{FieldID, SerializableField},
    proto::{reader::*, v1::RawCircuit},
};

pub struct CircuitReader<'a, F> {
    pub(in crate::core::proto::v1) f: &'a F,
    pub(in crate::core::proto::v1) field_id: FieldID,
    pub(in crate::core::proto::v1) max_total_terms: usize,
}

impl<'a, F: SerializableField> CircuitReader<'a, F> {
    pub fn new(f: &'a F, field_id: FieldID) -> Self {
        Self {
            f,
            field_id,
            max_total_terms: MAX_TOTAL_TERMS,
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
}

pub(in crate::core::proto::v1) fn validate_raw_circuit<F: SerializableField>(
    raw: &RawCircuit<F>,
) -> Result<(), String> {
    if raw.noutput > MAX_WIRES {
        return Err(format!("Excessive noutput: {}", raw.noutput));
    }
    if raw.npublic_input > MAX_WIRES {
        return Err(format!("Excessive npublic_input: {}", raw.npublic_input));
    }
    if raw.ninput > MAX_WIRES {
        return Err(format!("Excessive ninput: {}", raw.ninput));
    }
    if raw.npublic_input > raw.ninput {
        return Err(format!(
            "Invalid public input count: npublic_input ({}) exceeds ninput ({})",
            raw.npublic_input, raw.ninput
        ));
    }
    if raw.constants.len() > MAX_CONSTANTS {
        return Err(format!("Excessive constants: {}", raw.constants.len()));
    }
    if raw.layers.len() > MAX_LAYERS {
        return Err(format!("Excessive layers: {}", raw.layers.len()));
    }
    Ok(())
}
