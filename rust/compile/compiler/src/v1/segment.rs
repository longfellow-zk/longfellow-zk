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

use crate::{
    compile::compiler::segment::segment_stream,
    core::{
        algebra::SerializableField,
        proto::v1::{compute_id, Circuit, Layer, RawCircuit},
    },
};

/// Compresses a single layer using the Grouped Literals heuristic directly on deduplicated delta
/// indices.
///
/// Instead of a shortest-path Dynamic Programming search (which can segment the term sequence into
/// thousands of tiny, disjoint runs, leading to high token count and poor zstd back-references),
/// this algorithm uses a greedy "Grouped Literals" chunking strategy directly on deduplicated delta
/// indices:
/// 1. Unrolls all deduplicated delta indices (`u32`) in the layer.
/// 2. Identifies high-frequency macro sequences of length 32 (occurring >= 64 times) to build a
///    dictionary.
/// 3. Greedily tokens out matching dictionary macros.
/// 4. Groups any non-matching consecutive terms into contiguous literal runs.
/// 5. Sorts the deduplicated deltas and segments by frequency, and renumbers everything.
#[must_use]
pub fn segment_layer<F: SerializableField + Clone>(layer: &Layer<F>) -> Layer<F> {
    let mut terms = Vec::with_capacity(layer.num_terms());
    layer.for_each_delta_index(|idx| terms.push(idx));
    let stream = segment_stream(layer.deltas(), terms);
    Layer::new(
        layer.nw(),
        layer.logw(),
        stream.deltas,
        stream.segments,
        stream.tokens,
    )
}

/// Compresses an entire circuit by invoking `compress_layer` independently on each layer,
/// sorting constants by frequency across all layers, and renumbering everything.
///
/// Asserts that the canonical circuit ID (`compute_id`) remains identical before and after
/// compression, guaranteeing that evaluation order and semantic content of all terms across
/// all layers are strictly preserved.
pub fn segment_circuit<F: SerializableField + Clone>(f: &F, circuit: &Circuit<F>) -> Circuit<F> {
    let mut compressed_layers = Vec::with_capacity(circuit.raw.layers.len());

    for layer in &circuit.raw.layers {
        compressed_layers.push(segment_layer(layer));
    }

    // Sort constants by frequency across all compressed layers, and renumber.
    let num_constants = circuit.raw.constants.len();
    let mut const_counts = vec![0usize; num_constants];

    for layer in &compressed_layers {
        layer.for_each_delta_index(|d_idx| {
            let k_idx = layer.deltas()[d_idx as usize].k_index;
            const_counts[k_idx as usize] += 1;
        });
    }

    let mut const_order: Vec<usize> = (0..num_constants).collect();
    const_order.sort_by(|&a, &b| {
        const_counts[b]
            .cmp(&const_counts[a])
            .then_with(|| a.cmp(&b))
    });

    let mut old_to_new_const = vec![0u32; num_constants];
    let mut sorted_constants = Vec::with_capacity(num_constants);
    for (new_idx, &old_idx) in const_order.iter().enumerate() {
        old_to_new_const[old_idx] = new_idx as u32;
        sorted_constants.push(circuit.raw.constants[old_idx].clone());
    }

    // Renumber k_index in all deltas of all compressed layers
    for layer in &mut compressed_layers {
        for d in layer.deltas_mut() {
            d.k_index = old_to_new_const[d.k_index as usize];
        }
    }

    let new_raw = RawCircuit {
        ninput: circuit.raw.ninput,
        npublic_input: circuit.raw.npublic_input,
        noutput: circuit.raw.noutput,
        logv: circuit.raw.logv,
        subfield_boundary: circuit.raw.subfield_boundary,
        constants: sorted_constants,
        layers: compressed_layers,
    };

    // Verify that canonical circuit ID is invariant under compression.
    let new_id = compute_id(f, &new_raw);
    assert_eq!(new_id, circuit.id, "Circuit ID changed during compression!");

    Circuit {
        raw: new_raw,
        id: circuit.id,
    }
}
