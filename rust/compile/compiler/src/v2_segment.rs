// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compress native v2 record dictionaries without quadratic-record conversions.
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
    Layer {
        nw: layer.nw,
        logw: layer.logw,
        quadratic: compress(&layer.quadratic),
        quadratic_one: compress(&layer.quadratic_one),
        quadratic_minus_one: compress(&layer.quadratic_minus_one),
        quadratic_assertions: compress(&layer.quadratic_assertions),
        linear: compress(&layer.linear),
        linear_one: compress(&layer.linear_one),
        linear_minus_one: compress(&layer.linear_minus_one),
        linear_assertions: compress(&layer.linear_assertions),
        constant: compress(&layer.constant),
        constant_one: compress(&layer.constant_one),
        constant_minus_one: compress(&layer.constant_minus_one),
    }
}

/// Preserve expanded stream order and identity while compressing each class.
pub fn segment_circuit_v2<F: SerializableField + Clone>(f: &F, c: &Circuit<F>) -> Circuit<F> {
    let mut layers: Vec<_> = c.raw.layers.iter().map(layer).collect();
    let mut counts = vec![0usize; c.raw.constants.len()];
    macro_rules! count {
        ($stream:expr) => {
            for &token in &$stream.tokens {
                for &index in &$stream.segments[token as usize] {
                    counts[$stream.deltas[index as usize].k as usize] += 1;
                }
            }
        };
    }
    for layer in &layers {
        count!(layer.quadratic);
        count!(layer.linear);
        count!(layer.constant);
    }
    let mut order: Vec<_> = (0..counts.len()).collect();
    order.sort_by(|&a, &b| counts[b].cmp(&counts[a]).then_with(|| a.cmp(&b)));
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
        compute_id(f, &raw, c.coefficient_classes),
        c.id,
        "Circuit ID changed during compression!"
    );
    Circuit {
        raw,
        id: c.id,
        coefficient_classes: c.coefficient_classes,
    }
}
