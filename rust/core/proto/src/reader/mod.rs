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

pub mod lfc1;
pub mod lfc2;
mod lfc3;

use super::{FieldID, SerializableField};
use crate::core::proto::circuit::{Circuit, RawCircuit};

// Reader hardening constants: dimensioned for 5 million max wires and 20 million max terms
pub(super) const MAX_WIRES: usize = 5_000_000;
pub(super) const MAX_TERMS_PER_LAYER: usize = 20_000_000;
pub(super) const MAX_TOTAL_TERMS: usize = 20_000_000;
pub(super) const MAX_DELTAS: usize = 20_000_000;
pub(super) const MAX_CONSTANTS: usize = 5_000_000;
pub(super) const MAX_LAYERS: usize = 10_000;
pub(super) const MAX_LAYER_INPUTS: usize = 5_000_000;

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

    pub fn from_bytes_lfc3<'b>(
        &self,
        bytes: &'b [u8],
        enforce_circuit_id: bool,
    ) -> Result<(crate::core::proto::v2::Circuit<F>, &'b [u8]), String> {
        let mut cursor = bytes;
        let circuit = self.from_stream_lfc3(&mut cursor, enforce_circuit_id)?;
        Ok((circuit, cursor))
    }

    pub fn from_stream_lfc3<R: std::io::BufRead>(
        &self,
        stream: &mut R,
        enforce_circuit_id: bool,
    ) -> Result<crate::core::proto::v2::Circuit<F>, String> {
        lfc3::from_stream(self, stream, enforce_circuit_id)
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

    pub fn from_bytes_lfc1<'b>(
        &self,
        bytes: &'b [u8],
        enforce_circuit_id: bool,
    ) -> Result<(Circuit<F>, &'b [u8]), String> {
        let mut cursor = bytes;
        let circuit = self.from_stream_lfc1(&mut cursor, enforce_circuit_id)?;
        Ok((circuit, cursor))
    }

    pub fn from_bytes_lfc2<'b>(
        &self,
        bytes: &'b [u8],
        enforce_circuit_id: bool,
    ) -> Result<(Circuit<F>, &'b [u8]), String> {
        let mut cursor = bytes;
        let circuit = self.from_stream_lfc2(&mut cursor, enforce_circuit_id)?;
        Ok((circuit, cursor))
    }

    pub fn from_stream<R: std::io::BufRead>(
        &self,
        stream: &mut R,
        enforce_circuit_id: bool,
    ) -> Result<Circuit<F>, String> {
        let mut first = [0];
        stream
            .read_exact(&mut first)
            .map_err(|e| format!("Incomplete circuit header: {e}"))?;
        if first[0] == 1 {
            return lfc1::from_stream_lfc1_inner(self, stream, enforce_circuit_id);
        }
        let mut header = [first[0], 0, 0, 0];
        stream
            .read_exact(&mut header[1..])
            .map_err(|e| format!("Incomplete circuit header: {e}"))?;
        if &header != b"LFC2" {
            return Err("Unsupported legacy circuit format; use the v2 reader for LFC3".into());
        }
        lfc2::from_stream_lfc2_inner(self, stream, enforce_circuit_id)
    }

    pub fn from_stream_lfc1<R: std::io::BufRead>(
        &self,
        stream: &mut R,
        enforce_circuit_id: bool,
    ) -> Result<Circuit<F>, String> {
        let mut ver_buf = [0u8; 1];
        stream
            .read_exact(&mut ver_buf)
            .map_err(|_| "Empty or incomplete stream buffer".to_string())?;
        if ver_buf[0] != 1 {
            return Err(format!(
                "Unsupported LFC1 header: expected 1, got {}",
                ver_buf[0]
            ));
        }
        lfc1::from_stream_lfc1_inner(self, stream, enforce_circuit_id)
    }

    pub fn from_stream_lfc2<R: std::io::BufRead>(
        &self,
        stream: &mut R,
        enforce_circuit_id: bool,
    ) -> Result<Circuit<F>, String> {
        let mut header = [0u8; 4];
        stream
            .read_exact(&mut header)
            .map_err(|_| "Empty or incomplete stream buffer".to_string())?;
        if &header != b"LFC2" {
            return Err("expected LFC2 magic".into());
        }
        lfc2::from_stream_lfc2_inner(self, stream, enforce_circuit_id)
    }

    #[allow(dead_code)]
    pub(super) fn parse_circuit_id<R: std::io::BufRead>(
        &self,
        stream: &mut R,
        raw: &RawCircuit<F>,
    ) -> Result<[u8; 32], String> {
        let mut parsed_id = [0u8; 32];
        stream
            .read_exact(&mut parsed_id)
            .map_err(|e| format!("Failed to read circuit_id: {e}"))?;
        let computed_id = crate::core::proto::circuit::compute_id(self.f, raw);
        if parsed_id != computed_id {
            return Err(format!(
                "Circuit ID mismatch: expected {computed_id:?}, got {parsed_id:?}"
            ));
        }
        Ok(parsed_id)
    }
}

pub(super) fn validate_raw_circuit<F: SerializableField>(
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

#[cfg(test)]
mod tests {
    #[test]
    fn default_total_term_limit_is_unchanged() {
        let field = crate::compile::algebra::p256::P256Field::new();
        let reader = super::CircuitReader::new(&field, crate::core::proto::FieldID::P256);
        assert_eq!(reader.max_total_terms, 20_000_000);
    }
}

impl<'a, F: SerializableField> CircuitReader<'a, F> {
    /// V2 executes LFC3's concrete v2 streams only.
    pub fn from_bytes_v2<'b>(
        &self,
        bytes: &'b [u8],
        enforce_circuit_id: bool,
    ) -> Result<(crate::core::proto::v2::Circuit<F>, &'b [u8]), String> {
        self.from_bytes_lfc3(bytes, enforce_circuit_id)
    }
}
