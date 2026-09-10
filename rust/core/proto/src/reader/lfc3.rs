// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::io::BufRead;

use util::ceil_log2;

use super::CircuitReader;
use crate::{
    circuit::{Circuit, Layer, RawCircuit, TermDelta},
    writer::lfc3::TOKEN_PHRASE_LEN,
    SerializableField,
};

const TOKEN_ENCODING_FLAT: u32 = 0;
const TOKEN_ENCODING_PHRASES: u32 = 1;

pub(super) fn from_stream_lfc3_inner<R: BufRead, F: SerializableField>(
    reader: &CircuitReader<'_, F>,
    stream: &mut R,
    enforce_legacy_circuit_id: bool,
) -> Result<Circuit<F>, String> {
    let field_id = read_canonical_uleb28(stream)?;
    let noutput = read_count(stream, super::MAX_WIRES, "noutput")?;
    if noutput == 0 {
        return Err("Invalid noutput: expected at least one output".to_string());
    }
    let logv = ceil_log2(noutput);
    if !crate::sane_logw(logv) {
        return Err(format!(
            "Circuit logv {logv} exceeds MAX_LOGW {} or usize bit width",
            crate::MAX_LOGW
        ));
    }

    let ncopies = read_canonical_uleb28(stream)?;
    if ncopies != 1 {
        return Err(format!("Unsupported ncopies: expected 1, got {ncopies}"));
    }
    let npublic_input = read_count(stream, super::MAX_WIRES, "npublic_input")?;
    let subfield_boundary = read_count(stream, super::MAX_WIRES, "subfield_boundary")?;
    let ninput = read_count(stream, super::MAX_WIRES, "ninput")?;
    let layer_count = read_count(stream, super::MAX_LAYERS, "layer")?;

    if field_id != reader.field_id as u32 {
        return Err(format!(
            "Field ID mismatch: expected {}, got {field_id}",
            reader.field_id as u32
        ));
    }

    let constant_count = read_count(stream, super::MAX_CONSTANTS, "constant")?;
    let element_size = SerializableField::serialized_size_bytes(reader.f);
    let mut element_bytes = vec![0u8; element_size];
    let mut constants = Vec::with_capacity(constant_count);
    for _ in 0..constant_count {
        stream
            .read_exact(&mut element_bytes)
            .map_err(|error| format!("Failed to read constant: {error}"))?;
        constants.push(
            reader
                .f
                .bytes_to_element(&element_bytes)
                .map_err(|error| format!("Field deserialization error: {error:?}"))?,
        );
    }

    let mut layers = Vec::with_capacity(layer_count);
    let mut total_terms = 0usize;
    for _ in 0..layer_count {
        let logw = read_canonical_uleb28(stream)? as usize;
        if !crate::sane_logw(logw) {
            return Err(format!(
                "Layer logw {logw} exceeds MAX_LOGW {} or usize bit width",
                crate::MAX_LOGW
            ));
        }
        let nw = read_count(stream, super::MAX_LAYER_INPUTS, "layer input")?;

        let delta_count = read_count(stream, super::MAX_DELTAS, "delta")?;
        let mut deltas = Vec::with_capacity(delta_count);
        for _ in 0..delta_count {
            let g = decode_delta(read_canonical_uleb28(stream)?);
            let h0 = decode_delta(read_canonical_uleb28(stream)?);
            let h1 = decode_delta(read_canonical_uleb28(stream)?);
            let k_index = read_canonical_uleb28(stream)?;
            if k_index as usize >= constants.len() {
                return Err(format!(
                    "LFC3 delta k_index out of bounds: {k_index} >= {}",
                    constants.len()
                ));
            }
            deltas.push(TermDelta {
                g,
                h: [h0, h1],
                k_index,
            });
        }

        let segment_count = read_count(stream, super::MAX_DELTAS, "segment")?;
        let mut segment_symbols = 0usize;
        let mut segments = Vec::with_capacity(segment_count);
        for _ in 0..segment_count {
            let length = read_count(stream, super::MAX_TERMS_PER_LAYER, "segment length")?;
            segment_symbols = segment_symbols.saturating_add(length);
            if segment_symbols > super::MAX_TERMS_PER_LAYER {
                return Err(format!(
                    "LFC3 segment dictionary exceeds {} symbols",
                    super::MAX_TERMS_PER_LAYER
                ));
            }
            let mut segment = Vec::with_capacity(length);
            for _ in 0..length {
                let delta_index = read_canonical_uleb28(stream)?;
                if delta_index as usize >= deltas.len() {
                    return Err(format!(
                        "LFC3 delta index out of bounds: {delta_index} >= {}",
                        deltas.len()
                    ));
                }
                segment.push(delta_index);
            }
            segments.push(segment);
        }

        let encoding = read_canonical_uleb28(stream)?;
        let tokens = match encoding {
            TOKEN_ENCODING_FLAT => read_flat_tokens(stream, segments.len())?,
            TOKEN_ENCODING_PHRASES => read_phrase_tokens(stream, segments.len())?,
            _ => return Err(format!("Unsupported LFC3 token encoding: {encoding}")),
        };

        let mut layer_terms = 0usize;
        for &token in &tokens {
            layer_terms = layer_terms.saturating_add(segments[token as usize].len());
        }
        if layer_terms > super::MAX_TERMS_PER_LAYER {
            return Err(format!(
                "Excessive layer term count after LFC3 expansion: {layer_terms} (max {})",
                super::MAX_TERMS_PER_LAYER
            ));
        }
        total_terms = total_terms.saturating_add(layer_terms);
        if total_terms > super::MAX_TOTAL_TERMS {
            return Err(format!(
                "Total terms across layers {total_terms} exceeds MAX_TOTAL_TERMS {}",
                super::MAX_TOTAL_TERMS
            ));
        }

        layers.push(Layer::new(nw, logw, deltas, segments, tokens));
    }

    let mut id = [0u8; 32];
    stream
        .read_exact(&mut id)
        .map_err(|error| format!("Failed to read legacy circuit ID: {error}"))?;

    let raw = RawCircuit {
        ninput,
        npublic_input,
        noutput,
        logv,
        subfield_boundary,
        constants,
        layers,
    };
    super::validate_raw_circuit(&raw)?;

    if enforce_legacy_circuit_id && crate::circuit::compute_id(reader.f, &raw) != id {
        return Err("Legacy circuit ID verification failed".to_string());
    }
    Ok(Circuit { raw, id })
}

fn read_flat_tokens<R: BufRead>(stream: &mut R, segment_count: usize) -> Result<Vec<u32>, String> {
    let token_count = read_count(stream, super::MAX_TERMS_PER_LAYER, "flat token")?;
    let mut tokens = Vec::with_capacity(token_count);
    for _ in 0..token_count {
        let token = read_canonical_uleb28(stream)?;
        if token as usize >= segment_count {
            return Err(format!(
                "LFC3 segment token out of bounds: {token} >= {segment_count}"
            ));
        }
        tokens.push(token);
    }
    Ok(tokens)
}

fn read_phrase_tokens<R: BufRead>(
    stream: &mut R,
    segment_count: usize,
) -> Result<Vec<u32>, String> {
    let phrase_count = read_count(stream, super::MAX_TERMS_PER_LAYER, "token phrase")?;
    let mut phrase_symbols = 0usize;
    let mut phrases = Vec::with_capacity(phrase_count);
    for _ in 0..phrase_count {
        let length = read_count(stream, TOKEN_PHRASE_LEN, "token phrase length")?;
        if length == 0 {
            return Err("LFC3 token phrases must be nonempty".to_string());
        }
        phrase_symbols = phrase_symbols.saturating_add(length);
        if phrase_symbols > super::MAX_TERMS_PER_LAYER {
            return Err(format!(
                "LFC3 phrase dictionary exceeds {} symbols",
                super::MAX_TERMS_PER_LAYER
            ));
        }
        let mut phrase = Vec::with_capacity(length);
        for _ in 0..length {
            let segment_index = read_canonical_uleb28(stream)?;
            if segment_index as usize >= segment_count {
                return Err(format!(
                    "LFC3 phrase segment index out of bounds: {segment_index} >= {segment_count}"
                ));
            }
            phrase.push(segment_index);
        }
        phrases.push(phrase);
    }

    let root_count = read_count(stream, super::MAX_TERMS_PER_LAYER, "root phrase token")?;
    let mut expanded_count = 0usize;
    let mut root = Vec::with_capacity(root_count);
    for _ in 0..root_count {
        let phrase_index = read_canonical_uleb28(stream)?;
        if phrase_index as usize >= phrases.len() {
            return Err(format!(
                "LFC3 root phrase index out of bounds: {phrase_index} >= {}",
                phrases.len()
            ));
        }
        expanded_count = expanded_count.saturating_add(phrases[phrase_index as usize].len());
        if expanded_count > super::MAX_TERMS_PER_LAYER {
            return Err(format!(
                "LFC3 token expansion exceeds {} symbols",
                super::MAX_TERMS_PER_LAYER
            ));
        }
        root.push(phrase_index);
    }

    let mut tokens = Vec::with_capacity(expanded_count);
    for phrase_index in root {
        tokens.extend_from_slice(&phrases[phrase_index as usize]);
    }
    Ok(tokens)
}

fn read_count<R: BufRead>(stream: &mut R, maximum: usize, name: &str) -> Result<usize, String> {
    let value = read_canonical_uleb28(stream)? as usize;
    if value > maximum {
        return Err(format!("Excessive {name} count: {value} (max {maximum})"));
    }
    Ok(value)
}

/// Reads the unique shortest ULEB128 encoding of a 28-bit value.
fn read_canonical_uleb28<R: BufRead>(stream: &mut R) -> Result<u32, String> {
    let mut value = 0u32;
    for index in 0..4 {
        let mut byte = [0u8; 1];
        stream
            .read_exact(&mut byte)
            .map_err(|error| format!("Failed to read canonical ULEB128: {error}"))?;
        let payload = byte[0] & 0x7f;
        value |= u32::from(payload) << (7 * index);
        if byte[0] & 0x80 == 0 {
            if index > 0 && payload == 0 {
                return Err("Non-canonical ULEB128 encoding".to_string());
            }
            return Ok(value);
        }
    }
    Err("ULEB128 value exceeded the LFC3 28-bit limit".to_string())
}

#[inline(always)]
fn decode_delta(value: u32) -> u32 {
    (value >> 1) ^ ((value & 1).wrapping_neg())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_nonminimal_uleb() {
        let mut bytes = &[0x80, 0x00][..];
        assert!(read_canonical_uleb28(&mut bytes).is_err());
    }

    #[test]
    fn accepts_uleb_boundaries() {
        for (bytes, expected) in [
            (&[0x00][..], 0),
            (&[0x7f][..], 127),
            (&[0x80, 0x01][..], 128),
            (&[0xff, 0xff, 0xff, 0x7f][..], 0x0fff_ffff),
        ] {
            let mut input = bytes;
            assert_eq!(read_canonical_uleb28(&mut input), Ok(expected));
        }
    }

    #[test]
    fn expands_bounded_token_phrases() {
        // one phrase [segment 0, segment 1], referenced three times
        let mut input = &[1, 2, 0, 1, 3, 0, 0, 0][..];
        assert_eq!(
            read_phrase_tokens(&mut input, 2),
            Ok(vec![0, 1, 0, 1, 0, 1])
        );
        assert!(input.is_empty());
    }

    #[test]
    fn rejects_zero_outputs_without_panicking() {
        let field = compile_algebra::p256::P256Field::new();
        let reader = CircuitReader::new(&field, crate::FieldID::P256);
        let mut input = &[crate::FieldID::P256 as u8, 0][..];
        assert!(from_stream_lfc3_inner(&reader, &mut input, false).is_err());
    }
}
