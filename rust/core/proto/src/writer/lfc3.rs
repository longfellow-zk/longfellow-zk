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

//! Experimental LFC3 writer.
//!
//! LFC3 adds one bounded dictionary level over LFC2's segment-token stream.
//! It is designed for circuits made from many copies of a subcircuit: the
//! term-delta and segment dictionaries remain exactly as in LFC2, while long
//! repeated sequences of segment references are stored only once.  Expansion
//! depth is fixed at two dictionaries, avoiding recursive grammar validation
//! in a future verified decoder.

use std::collections::HashMap;

use super::CircuitWriter;
use crate::{
    circuit::Circuit,
    uleb::{serialize_uleb128_max4, serialize_uleb128_max4_u32, uleb128_len_u32},
    SerializableField,
};

/// Phrase length selected by the canonical writer and enforced as the decoder
/// maximum, keeping expansion depth and local fan-out statically bounded.
pub const TOKEN_PHRASE_LEN: usize = 16;

const TOKEN_ENCODING_FLAT: u32 = 0;
const TOKEN_ENCODING_PHRASES: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenPhraseEncoding {
    pub phrases: Vec<Vec<u32>>,
    pub root_tokens: Vec<u32>,
}

/// The canonical token representation selected by the LFC3 writer.
///
/// This is public so formal-certificate generators can emit the exact compact
/// value that the verified Lean decoder must recover, rather than duplicating
/// the writer's size-selection rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalTokenEncoding {
    Flat(Vec<u32>),
    Phrases(TokenPhraseEncoding),
}

impl TokenPhraseEncoding {
    #[must_use]
    pub fn dictionary_symbols(&self) -> usize {
        self.phrases.iter().map(Vec::len).sum()
    }

    #[must_use]
    pub fn expanded_len(&self) -> usize {
        self.root_tokens
            .iter()
            .map(|&token| self.phrases[token as usize].len())
            .sum()
    }

    #[must_use]
    pub fn expand(&self) -> Vec<u32> {
        let mut expanded = Vec::with_capacity(self.expanded_len());
        for &token in &self.root_tokens {
            expanded.extend_from_slice(&self.phrases[token as usize]);
        }
        expanded
    }
}

#[inline(always)]
fn zigzag_encode_delta(delta: u32) -> u32 {
    (delta << 1) ^ ((delta as i32 >> 31) as u32)
}

/// Builds the deterministic second-level dictionary used by LFC3.
///
/// Candidate phrases are full `phrase_len` windows whose stable hash occurs
/// at least twice.  Hash equality is only a filter: a candidate is used after
/// an exact slice comparison, so collisions can only reduce compression.
#[must_use]
pub fn encode_token_phrases(tokens: &[u32], phrase_len: usize) -> TokenPhraseEncoding {
    assert!(phrase_len > 0, "LFC3 phrase length must be nonzero");
    if tokens.is_empty() {
        return TokenPhraseEncoding {
            phrases: Vec::new(),
            root_tokens: Vec::new(),
        };
    }

    let mut window_occurrences: HashMap<u64, (usize, usize)> = HashMap::new();
    if tokens.len() >= phrase_len {
        for start in 0..=tokens.len() - phrase_len {
            let hash = stable_window_hash(&tokens[start..start + phrase_len]);
            window_occurrences
                .entry(hash)
                .and_modify(|(count, _)| *count += 1)
                .or_insert((1, start));
        }
    }

    let is_repeated_at = |start: usize| -> bool {
        if start + phrase_len > tokens.len() {
            return false;
        }
        let hash = stable_window_hash(&tokens[start..start + phrase_len]);
        let Some(&(count, first)) = window_occurrences.get(&hash) else {
            return false;
        };
        count >= 2 && tokens[start..start + phrase_len] == tokens[first..first + phrase_len]
    };

    let mut phrases: Vec<Vec<u32>> = Vec::new();
    let mut phrase_ids: HashMap<Vec<u32>, u32> = HashMap::new();
    let mut root_tokens = Vec::new();
    let mut start = 0usize;

    while start < tokens.len() {
        let end = if is_repeated_at(start) {
            start + phrase_len
        } else {
            let limit = (start + phrase_len).min(tokens.len());
            let mut end = start + 1;
            while end < limit && !is_repeated_at(end) {
                end += 1;
            }
            end
        };

        let phrase = &tokens[start..end];
        let phrase_id = if let Some(&id) = phrase_ids.get(phrase) {
            id
        } else {
            let id = u32::try_from(phrases.len()).expect("too many LFC3 token phrases");
            let owned = phrase.to_vec();
            phrases.push(owned.clone());
            phrase_ids.insert(owned, id);
            id
        };
        root_tokens.push(phrase_id);
        start = end;
    }

    // Frequent phrases get the smallest ULEB128 identifiers.
    let mut counts = vec![0usize; phrases.len()];
    for &token in &root_tokens {
        counts[token as usize] += 1;
    }
    let mut order: Vec<usize> = (0..phrases.len()).collect();
    order.sort_by(|&left, &right| {
        counts[right]
            .cmp(&counts[left])
            .then_with(|| left.cmp(&right))
    });

    let mut old_to_new = vec![0u32; phrases.len()];
    let mut sorted_phrases = Vec::with_capacity(phrases.len());
    for (new, &old) in order.iter().enumerate() {
        old_to_new[old] = u32::try_from(new).expect("too many LFC3 token phrases");
        sorted_phrases.push(std::mem::take(&mut phrases[old]));
    }
    for token in &mut root_tokens {
        *token = old_to_new[*token as usize];
    }

    TokenPhraseEncoding {
        phrases: sorted_phrases,
        root_tokens,
    }
}

#[inline]
#[must_use]
fn stable_window_hash(window: &[u32]) -> u64 {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;
    let mut hash = OFFSET;
    for &word in window {
        for byte in word.to_le_bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(PRIME);
        }
    }
    hash
}

#[must_use]
fn flat_wire_len(tokens: &[u32]) -> usize {
    1 + uleb128_len_u32(tokens.len() as u32) as usize
        + tokens
            .iter()
            .map(|&token| uleb128_len_u32(token) as usize)
            .sum::<usize>()
}

#[must_use]
fn phrase_wire_len(encoding: &TokenPhraseEncoding) -> usize {
    1 + uleb128_len_u32(encoding.phrases.len() as u32) as usize
        + encoding
            .phrases
            .iter()
            .map(|phrase| {
                uleb128_len_u32(phrase.len() as u32) as usize
                    + phrase
                        .iter()
                        .map(|&token| uleb128_len_u32(token) as usize)
                        .sum::<usize>()
            })
            .sum::<usize>()
        + uleb128_len_u32(encoding.root_tokens.len() as u32) as usize
        + encoding
            .root_tokens
            .iter()
            .map(|&token| uleb128_len_u32(token) as usize)
            .sum::<usize>()
}

/// Selects exactly the encoding used on the LFC3 wire.
///
/// **The phrase dictionary is disabled.** It is a wire-size optimization that does not pay for
/// itself anywhere it was supposed to:
///
/// * *transport* -- the shipped artifact is zstd'd, and after zstd the phrase encoding is
///   **larger**: 366,200 bytes against flat's 350,799 for the mdoc hash payload, because zstd
///   already exploits the same repeated token runs;
/// * *prover / verifier* -- LFC3 is not selected by either, so there is no runtime path at all;
/// * *formal checking* -- it saves 18% of the committed payload, which is 52 of 288 pages for the
///   mdoc hash circuit: about 11 minutes of a ~7.2-hour Lean build, or 2.8%.  It cannot touch the
///   expansion work, which is 7,757,579 terms either way and is where the hours actually go.
///
/// What LFC3 *does* buy -- a canonical uncompressed payload with a page-Merkle root and a
/// verified Lean decoder -- is untouched by this, and is the reason the format exists.
///
/// `Flat` is exactly LFC2's token encoding, so with this in force the committed payload is
/// LFC2-equivalent in content while the magic, header, commitment and decoder are unchanged.
/// Every existing artifact keeps its proofs; `Lfc3.TokenEncoding.phrases` simply stops being
/// emitted. Restore the selection by deleting the early return.
#[must_use]
pub fn canonical_token_encoding(tokens: &[u32]) -> CanonicalTokenEncoding {
    return CanonicalTokenEncoding::Flat(tokens.to_vec());

    #[allow(unreachable_code)]
    {
        let phrase_encoding = encode_token_phrases(tokens, TOKEN_PHRASE_LEN);
        if phrase_wire_len(&phrase_encoding) < flat_wire_len(tokens) {
            CanonicalTokenEncoding::Phrases(phrase_encoding)
        } else {
            CanonicalTokenEncoding::Flat(tokens.to_vec())
        }
    }
}

pub(super) fn to_bytes_lfc3<F: SerializableField>(
    writer: &CircuitWriter<'_, F>,
    circuit: &Circuit<F>,
) -> Vec<u8> {
    let mut bytes = Vec::new();

    bytes.extend_from_slice(b"LFC3");
    serialize_uleb128_max4(&mut bytes, writer.field_id as usize);
    serialize_uleb128_max4(&mut bytes, circuit.raw.noutput);
    serialize_uleb128_max4(&mut bytes, 1);
    serialize_uleb128_max4(&mut bytes, circuit.raw.npublic_input);
    serialize_uleb128_max4(&mut bytes, circuit.raw.subfield_boundary);
    serialize_uleb128_max4(&mut bytes, circuit.raw.ninput);
    serialize_uleb128_max4(&mut bytes, circuit.raw.layers.len());

    serialize_uleb128_max4(&mut bytes, circuit.raw.constants.len());
    for value in &circuit.raw.constants {
        writer.serialize_elt(&mut bytes, value);
    }

    for layer in &circuit.raw.layers {
        assert!(crate::sane_logw(layer.logw()), "layer logw must be sane");
        serialize_uleb128_max4(&mut bytes, layer.logw());
        serialize_uleb128_max4(&mut bytes, layer.nw());

        serialize_uleb128_max4(&mut bytes, layer.deltas().len());
        for delta in layer.deltas() {
            serialize_uleb128_max4_u32(&mut bytes, zigzag_encode_delta(delta.g));
            serialize_uleb128_max4_u32(&mut bytes, zigzag_encode_delta(delta.h[0]));
            serialize_uleb128_max4_u32(&mut bytes, zigzag_encode_delta(delta.h[1]));
            serialize_uleb128_max4_u32(&mut bytes, delta.k_index);
        }

        serialize_uleb128_max4(&mut bytes, layer.delta_segments().len());
        for segment in layer.delta_segments() {
            serialize_uleb128_max4(&mut bytes, segment.len());
            for &delta_index in segment {
                serialize_uleb128_max4_u32(&mut bytes, delta_index);
            }
        }

        match canonical_token_encoding(layer.delta_tokens()) {
            CanonicalTokenEncoding::Phrases(phrase_encoding) => {
                serialize_uleb128_max4_u32(&mut bytes, TOKEN_ENCODING_PHRASES);
                serialize_uleb128_max4(&mut bytes, phrase_encoding.phrases.len());
                for phrase in &phrase_encoding.phrases {
                    serialize_uleb128_max4(&mut bytes, phrase.len());
                    for &segment_index in phrase {
                        serialize_uleb128_max4_u32(&mut bytes, segment_index);
                    }
                }
                serialize_uleb128_max4(&mut bytes, phrase_encoding.root_tokens.len());
                for &phrase_index in &phrase_encoding.root_tokens {
                    serialize_uleb128_max4_u32(&mut bytes, phrase_index);
                }
            }
            CanonicalTokenEncoding::Flat(tokens) => {
                serialize_uleb128_max4_u32(&mut bytes, TOKEN_ENCODING_FLAT);
                serialize_uleb128_max4(&mut bytes, tokens.len());
                for segment_index in tokens {
                    serialize_uleb128_max4_u32(&mut bytes, segment_index);
                }
            }
        }
    }

    // Retained for interoperability with the current Circuit type.  The new
    // verifier protocol treats the external formal commitment as authoritative.
    bytes.extend_from_slice(&circuit.id);
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn phrase_encoding_roundtrips_repeated_and_literal_regions() {
        let repeated: Vec<u32> = (0..TOKEN_PHRASE_LEN as u32).collect();
        let mut tokens = vec![700, 701, 702];
        for _ in 0..40 {
            tokens.extend_from_slice(&repeated);
        }
        tokens.extend([900, 901]);

        let encoded = encode_token_phrases(&tokens, TOKEN_PHRASE_LEN);
        assert_eq!(encoded.expand(), tokens);
        assert!(encoded.dictionary_symbols() + encoded.root_tokens.len() < tokens.len() / 4);
    }

    #[test]
    fn phrase_encoding_is_deterministic() {
        let tokens: Vec<u32> = (0..10_000).map(|i| ((i / 64) % 7) as u32).collect();
        assert_eq!(
            encode_token_phrases(&tokens, TOKEN_PHRASE_LEN),
            encode_token_phrases(&tokens, TOKEN_PHRASE_LEN)
        );
    }
}
