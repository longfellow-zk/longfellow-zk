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

//! Measures the experimental formal circuit payload on a checked-in mdoc
//! artifact.  This is deliberately not part of prover/verifier selection.

use core_proto::{
    commitment::{FormalCircuitCommitment, FORMAL_PAGE_SIZE},
    writer::{lfc3::encode_token_phrases, CircuitWriter},
    FieldID, Layer, SerializableField, TermDelta,
};
use mdoc_zk_runtime::proto::decompress_circuits;
use std::collections::HashMap;
use std::time::Instant;

const DEFAULT_MDOC_HASH: &str = "5aebdaaafe17296a3ef3ca6c80c6e7505e09291897c39700410a365fb278e460";

fn main() {
    let hash = std::env::args()
        .nth(1)
        .unwrap_or_else(|| DEFAULT_MDOC_HASH.to_string());
    let compressed = mdoc_zk_artifacts::load_circuit_lfa2(&hash);
    let p256 = runtime_algebra::p256::P256Field::new();
    let gf2 = runtime_algebra::gf2_128::Gf2_128Field::new();
    let (sig, hash_circuit) =
        decompress_circuits(&compressed, &p256, &gf2).expect("decode checked-in mdoc artifact");

    println!("mdoc artifact {hash}: transport={} bytes", compressed.len());
    measure_circuit("sig", &p256, FieldID::P256, &sig);
    measure_circuit("hash", &gf2, FieldID::Gf2_128, &hash_circuit);
}

fn measure_circuit<F: SerializableField>(
    name: &str,
    field: &F,
    field_id: FieldID,
    circuit: &core_proto::circuit::Circuit<F>,
) {
    let writer = CircuitWriter::new(field, field_id);
    let lfc2 = writer.to_bytes_lfc2(circuit);
    let write_start = Instant::now();
    let lfc3 = writer.to_bytes_lfc3(circuit);
    let write_elapsed = write_start.elapsed();
    let lfc2_zstd = zstd::encode_all(&lfc2[..], mdoc_zk_circuits::config::K_ZSTD_LEVEL)
        .expect("compress LFC2 measurement");
    let lfc3_zstd = zstd::encode_all(&lfc3[..], mdoc_zk_circuits::config::K_ZSTD_LEVEL)
        .expect("compress LFC3 measurement");
    let commit_start = Instant::now();
    let commitment = FormalCircuitCommitment::new(&lfc3);
    let commit_elapsed = commit_start.elapsed();
    let reader = core_proto::reader::CircuitReader::new(field, field_id);
    let decode_start = Instant::now();
    let decoded = reader
        .from_bytes_lfc3_pinned(&lfc3, &commitment.root)
        .expect("verify and decode generated LFC3");
    let decode_elapsed = decode_start.elapsed();
    assert_eq!(decoded.raw.layers.len(), circuit.raw.layers.len());

    println!(
        "{name}: terms={} LFC2={} LFC3={} ({:.2}% of LFC2), zstd2={} zstd3={}, pages={} ({} bytes/page)",
        circuit.raw.layers.iter().map(Layer::num_terms).sum::<usize>(),
        lfc2.len(),
        lfc3.len(),
        100.0 * lfc3.len() as f64 / lfc2.len() as f64,
        lfc2_zstd.len(),
        lfc3_zstd.len(),
        commitment.page_count,
        FORMAL_PAGE_SIZE,
    );
    println!("{name}: formal root {}", hex(&commitment.root));
    println!(
        "{name}: LFC3 write={write_elapsed:?} commit={commit_elapsed:?} committed_decode={decode_elapsed:?}"
    );

    for phrase_len in [16, 32, 64, 128, 256] {
        let mut source = 0usize;
        let mut dictionary = 0usize;
        let mut roots = 0usize;
        let mut wire_bytes = 0usize;
        let mut useful_layers = 0usize;
        for layer in &circuit.raw.layers {
            let tokens = layer.delta_tokens();
            let encoding = encode_token_phrases(tokens, phrase_len);
            let flat_len = flat_wire_len(tokens);
            let phrase_len_bytes = phrase_wire_len(&encoding);
            source += tokens.len();
            dictionary += encoding.dictionary_symbols();
            roots += encoding.root_tokens.len();
            wire_bytes += flat_len.min(phrase_len_bytes);
            useful_layers += usize::from(phrase_len_bytes < flat_len);
            assert_eq!(encoding.expand(), tokens);
        }
        println!(
            "{name}: phrase={phrase_len:3} source_tokens={source} dictionary_symbols={dictionary} root_tokens={roots} selected_wire_bytes={wire_bytes} useful_layers={useful_layers}"
        );

        let local_uleb = circuit
            .raw
            .layers
            .iter()
            .map(|layer| local_grammar_wire_len(layer, phrase_len, false))
            .sum::<usize>();
        let local_packed = circuit
            .raw
            .layers
            .iter()
            .map(|layer| local_grammar_wire_len(layer, phrase_len, true))
            .sum::<usize>();
        println!(
            "{name}: local={phrase_len:3} layer_wire_uleb={local_uleb} layer_wire_bitpacked={local_packed} ({:.2}% of ULEB)",
            100.0 * local_packed as f64 / local_uleb as f64,
        );

        let global = GlobalDictionary::build(&circuit.raw.layers, phrase_len);
        println!(
            "{name}: global={phrase_len:3} deltas={} segment_symbols={} segments={} phrase_symbols={} phrases={} roots={} grammar_wire_bytes={} expanded_tokens={}",
            global.deltas.len(),
            global.segments.iter().map(Vec::len).sum::<usize>(),
            global.segments.len(),
            global.phrases.iter().map(Vec::len).sum::<usize>(),
            global.phrases.len(),
            global.layer_roots.iter().map(Vec::len).sum::<usize>(),
            global.wire_len(),
            global.expanded_tokens(),
        );
    }
}

fn local_grammar_wire_len<F: SerializableField>(
    layer: &Layer<F>,
    phrase_len: usize,
    bitpacked: bool,
) -> usize {
    let count_len = |value: usize| core_proto::uleb128_len_u32(value as u32) as usize;
    let id_len = |value: u32| core_proto::uleb128_len_u32(value) as usize;
    let phrases = encode_token_phrases(layer.delta_tokens(), phrase_len);

    let delta_bytes = layer
        .deltas()
        .iter()
        .map(|delta| {
            id_len(zigzag(delta.g))
                + id_len(zigzag(delta.h[0]))
                + id_len(zigzag(delta.h[1]))
                + id_len(delta.k_index)
        })
        .sum::<usize>();
    let segment_symbols = layer.delta_segments().iter().map(Vec::len).sum::<usize>();
    let phrase_symbols = phrases.dictionary_symbols();

    let segments_bytes = if bitpacked {
        layer
            .delta_segments()
            .iter()
            .map(|segment| count_len(segment.len()))
            .sum::<usize>()
            + packed_len(segment_symbols, bits_for(layer.deltas().len()))
    } else {
        layer
            .delta_segments()
            .iter()
            .map(|segment| {
                count_len(segment.len()) + segment.iter().map(|&id| id_len(id)).sum::<usize>()
            })
            .sum()
    };
    let phrases_bytes = if bitpacked {
        phrases
            .phrases
            .iter()
            .map(|phrase| count_len(phrase.len()))
            .sum::<usize>()
            + packed_len(phrase_symbols, bits_for(layer.delta_segments().len()))
            + packed_len(phrases.root_tokens.len(), bits_for(phrases.phrases.len()))
    } else {
        phrases
            .phrases
            .iter()
            .map(|phrase| {
                count_len(phrase.len()) + phrase.iter().map(|&id| id_len(id)).sum::<usize>()
            })
            .sum::<usize>()
            + phrases
                .root_tokens
                .iter()
                .map(|&id| id_len(id))
                .sum::<usize>()
    };

    count_len(layer.logw())
        + count_len(layer.nw())
        + count_len(layer.deltas().len())
        + delta_bytes
        + count_len(layer.delta_segments().len())
        + segments_bytes
        + count_len(phrases.phrases.len())
        + phrases_bytes
        + count_len(phrases.root_tokens.len())
}

fn bits_for(count: usize) -> usize {
    if count <= 1 {
        0
    } else {
        usize::BITS as usize - (count - 1).leading_zeros() as usize
    }
}

fn packed_len(count: usize, width: usize) -> usize {
    count.saturating_mul(width).div_ceil(8)
}

struct GlobalDictionary {
    deltas: Vec<TermDelta>,
    segments: Vec<Vec<u32>>,
    phrases: Vec<Vec<u32>>,
    layer_roots: Vec<Vec<u32>>,
}

impl GlobalDictionary {
    fn build<F: SerializableField>(layers: &[Layer<F>], phrase_len: usize) -> Self {
        let mut deltas = Vec::new();
        let mut delta_ids = HashMap::new();
        let mut segments = Vec::new();
        let mut segment_ids = HashMap::new();
        let mut layer_segment_tokens = Vec::with_capacity(layers.len());

        for layer in layers {
            let mut local_to_global_delta = Vec::with_capacity(layer.deltas().len());
            for &delta in layer.deltas() {
                let id = if let Some(&id) = delta_ids.get(&delta) {
                    id
                } else {
                    let id = deltas.len() as u32;
                    deltas.push(delta);
                    delta_ids.insert(delta, id);
                    id
                };
                local_to_global_delta.push(id);
            }

            let mut local_to_global_segment = Vec::with_capacity(layer.delta_segments().len());
            for segment in layer.delta_segments() {
                let global_segment: Vec<u32> = segment
                    .iter()
                    .map(|&id| local_to_global_delta[id as usize])
                    .collect();
                let id = if let Some(&id) = segment_ids.get(&global_segment) {
                    id
                } else {
                    let id = segments.len() as u32;
                    segments.push(global_segment.clone());
                    segment_ids.insert(global_segment, id);
                    id
                };
                local_to_global_segment.push(id);
            }

            layer_segment_tokens.push(
                layer
                    .delta_tokens()
                    .iter()
                    .map(|&id| local_to_global_segment[id as usize])
                    .collect::<Vec<_>>(),
            );
        }

        let mut phrases = Vec::new();
        let mut phrase_ids = HashMap::new();
        let mut layer_roots = Vec::with_capacity(layers.len());
        for tokens in &layer_segment_tokens {
            let local = encode_token_phrases(tokens, phrase_len);
            let mut local_to_global = Vec::with_capacity(local.phrases.len());
            for phrase in local.phrases {
                let id = if let Some(&id) = phrase_ids.get(&phrase) {
                    id
                } else {
                    let id = phrases.len() as u32;
                    phrases.push(phrase.clone());
                    phrase_ids.insert(phrase, id);
                    id
                };
                local_to_global.push(id);
            }
            layer_roots.push(
                local
                    .root_tokens
                    .iter()
                    .map(|&id| local_to_global[id as usize])
                    .collect(),
            );
        }

        let mut result = Self {
            deltas,
            segments,
            phrases,
            layer_roots,
        };
        result.frequency_sort();
        result
    }

    fn frequency_sort(&mut self) {
        let mut phrase_counts = vec![0usize; self.phrases.len()];
        for roots in &self.layer_roots {
            for &id in roots {
                phrase_counts[id as usize] += 1;
            }
        }
        let phrase_map = reorder(&mut self.phrases, &phrase_counts);
        for roots in &mut self.layer_roots {
            for id in roots {
                *id = phrase_map[*id as usize];
            }
        }

        let mut segment_counts = vec![0usize; self.segments.len()];
        for phrase in &self.phrases {
            for &id in phrase {
                segment_counts[id as usize] += 1;
            }
        }
        let segment_map = reorder(&mut self.segments, &segment_counts);
        for phrase in &mut self.phrases {
            for id in phrase {
                *id = segment_map[*id as usize];
            }
        }

        let mut delta_counts = vec![0usize; self.deltas.len()];
        for segment in &self.segments {
            for &id in segment {
                delta_counts[id as usize] += 1;
            }
        }
        let delta_map = reorder(&mut self.deltas, &delta_counts);
        for segment in &mut self.segments {
            for id in segment {
                *id = delta_map[*id as usize];
            }
        }
    }

    fn wire_len(&self) -> usize {
        let count_len = |value: usize| core_proto::uleb128_len_u32(value as u32) as usize;
        let id_len = |value: u32| core_proto::uleb128_len_u32(value) as usize;
        count_len(self.deltas.len())
            + self
                .deltas
                .iter()
                .map(|delta| {
                    id_len(zigzag(delta.g))
                        + id_len(zigzag(delta.h[0]))
                        + id_len(zigzag(delta.h[1]))
                        + id_len(delta.k_index)
                })
                .sum::<usize>()
            + count_len(self.segments.len())
            + self
                .segments
                .iter()
                .map(|segment| {
                    count_len(segment.len()) + segment.iter().map(|&id| id_len(id)).sum::<usize>()
                })
                .sum::<usize>()
            + count_len(self.phrases.len())
            + self
                .phrases
                .iter()
                .map(|phrase| {
                    count_len(phrase.len()) + phrase.iter().map(|&id| id_len(id)).sum::<usize>()
                })
                .sum::<usize>()
            + self
                .layer_roots
                .iter()
                .map(|roots| {
                    2 + count_len(roots.len()) + roots.iter().map(|&id| id_len(id)).sum::<usize>()
                })
                .sum::<usize>()
    }

    fn expanded_tokens(&self) -> usize {
        self.layer_roots
            .iter()
            .flat_map(|roots| roots.iter())
            .map(|&phrase| self.phrases[phrase as usize].len())
            .sum()
    }
}

fn reorder<T: Clone>(values: &mut Vec<T>, counts: &[usize]) -> Vec<u32> {
    let mut order: Vec<usize> = (0..values.len()).collect();
    order.sort_by(|&left, &right| {
        counts[right]
            .cmp(&counts[left])
            .then_with(|| left.cmp(&right))
    });
    let mut mapping = vec![0u32; values.len()];
    let mut sorted = Vec::with_capacity(values.len());
    for (new, &old) in order.iter().enumerate() {
        mapping[old] = new as u32;
    }
    sorted.extend(order.iter().map(|&old| values[old].clone()));
    *values = sorted;
    mapping
}

fn zigzag(delta: u32) -> u32 {
    (delta << 1) ^ ((delta as i32 >> 31) as u32)
}

fn flat_wire_len(tokens: &[u32]) -> usize {
    1 + core_proto::uleb128_len_u32(tokens.len() as u32) as usize
        + tokens
            .iter()
            .map(|&token| core_proto::uleb128_len_u32(token) as usize)
            .sum::<usize>()
}

fn phrase_wire_len(encoding: &core_proto::writer::lfc3::TokenPhraseEncoding) -> usize {
    1 + core_proto::uleb128_len_u32(encoding.phrases.len() as u32) as usize
        + encoding
            .phrases
            .iter()
            .map(|phrase| {
                core_proto::uleb128_len_u32(phrase.len() as u32) as usize
                    + phrase
                        .iter()
                        .map(|&token| core_proto::uleb128_len_u32(token) as usize)
                        .sum::<usize>()
            })
            .sum::<usize>()
        + core_proto::uleb128_len_u32(encoding.root_tokens.len() as u32) as usize
        + encoding
            .root_tokens
            .iter()
            .map(|&token| core_proto::uleb128_len_u32(token) as usize)
            .sum::<usize>()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
