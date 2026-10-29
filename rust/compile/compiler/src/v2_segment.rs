// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compress the three native v2 streams.
use std::{collections::HashMap, hash::Hash};

use crate::core::proto::{
    v2::{compute_id, Circuit, Layer, Stream},
    SerializableField,
};

fn compress<T: Copy + Eq + Hash>(stream: &Stream<T>) -> Stream<T> {
    let mut dictionary = HashMap::new();
    let mut deltas = Vec::new();
    let mut terms = Vec::with_capacity(stream.num_terms());
    for &token in &stream.tokens {
        for &index in &stream.segments[token as usize] {
            let term = stream.deltas[index as usize];
            let index = *dictionary.entry(term).or_insert_with(|| {
                let index = deltas.len() as u32;
                deltas.push(term);
                index
            });
            terms.push(index);
        }
    }
    super::segment::segment_stream(&deltas, terms)
}

fn layer(layer: &Layer) -> Layer {
    Layer::new(
        layer.nw,
        compress(&layer.quadratic),
        compress(&layer.linear),
        compress(&layer.constant),
    )
}

/// Preserve expanded stream order and identity while compressing each stream.
pub fn segment_circuit_v2<F: SerializableField>(f: &F, c: &Circuit<F>) -> Circuit<F> {
    let mut layers: Vec<_> = c.raw.layers.iter().map(layer).collect();
    let mut counts = vec![0usize; c.raw.constants.len()];
    for layer in &layers {
        for &token in &layer.quadratic.tokens {
            for &index in &layer.quadratic.segments[token as usize] {
                counts[layer.quadratic.deltas[index as usize].k as usize] += 1;
            }
        }
        for &token in &layer.linear.tokens {
            for &index in &layer.linear.segments[token as usize] {
                counts[layer.linear.deltas[index as usize].k as usize] += 1;
            }
        }
        for &token in &layer.constant.tokens {
            for &index in &layer.constant.segments[token as usize] {
                counts[layer.constant.deltas[index as usize].k as usize] += 1;
            }
        }
    }
    let mut order: Vec<_> = (0..counts.len()).collect();
    // Indices zero, one, and minus one are canonical; reorder only other coefficients.
    order[3..].sort_by(|&a, &b| counts[b].cmp(&counts[a]).then_with(|| a.cmp(&b)));
    let mut mapping = vec![0; counts.len()];
    let constants = order
        .into_iter()
        .enumerate()
        .map(|(new, old)| {
            mapping[old] = new as u32;
            c.raw.constants[old].clone()
        })
        .collect();
    for layer in &mut layers {
        for d in &mut layer.quadratic.deltas {
            d.k = mapping[d.k as usize];
        }
        for d in &mut layer.linear.deltas {
            d.k = mapping[d.k as usize];
        }
        for d in &mut layer.constant.deltas {
            d.k = mapping[d.k as usize];
        }
    }
    let raw = crate::core::proto::v2::RawCircuit {
        ninput: c.raw.ninput,
        npublic_input: c.raw.npublic_input,
        noutput: c.raw.noutput,
        logv: c.raw.logv,
        subfield_boundary: c.raw.subfield_boundary,
        constants,
        layers,
    };
    assert_eq!(
        compute_id(f, &raw),
        c.id,
        "Circuit ID changed during compression!"
    );
    Circuit { raw, id: c.id }
}
