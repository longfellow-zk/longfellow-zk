// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compress the three native v2 streams.
use std::{collections::HashMap, hash::Hash};

use crate::core::proto::{
    v2::{Circuit, Layer, RawCircuit, Stream},
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
    let compressed = super::segment::segment_stream(&deltas, terms);
    Stream {
        deltas: compressed.deltas,
        segments: compressed.segments.into(),
        tokens: compressed.tokens,
    }
}

fn layer(layer: &Layer, classes: &[crate::core::proto::v2::CoefficientClass]) -> Layer {
    Layer::with_assertions(
        layer.nw,
        compress(&layer.quadratic),
        compress(&layer.linear),
        compress(&layer.constant),
        |k| classes[k as usize] == crate::core::proto::v2::CoefficientClass::Zero,
    )
}

/// Preserve expanded stream order, compress the identity-free circuit, then
/// compute the ID of its final representation.
pub fn segment_circuit_v2<F: SerializableField>(f: &F, c: RawCircuit<F>) -> Circuit<F> {
    let classes = crate::core::proto::v2::classify_constants(f, &c.constants);
    let mut layers: Vec<_> = c.layers.iter().map(|l| layer(l, &classes)).collect();
    let mut counts = vec![0usize; c.constants.len()];
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
    order.sort_by(|&a, &b| counts[b].cmp(&counts[a]).then_with(|| a.cmp(&b)));
    let mut mapping = vec![0; counts.len()];
    let constants = order
        .into_iter()
        .enumerate()
        .map(|(new, old)| {
            mapping[old] = new as u32;
            c.constants[old].clone()
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
    let raw = crate::core::proto::v2::RawCircuitBuilder {
        ninput: c.ninput,
        npublic_input: c.npublic_input,
        noutput: c.noutput,
        logv: c.logv,
        constants,
        layers,
    }
    .build();
    Circuit::from_raw(f, raw)
}
