// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
//! Segmentation control: same phrases and executions, different dictionary order.
use core_proto::{Layer, SerializableField};
use std::cmp::Reverse;

pub fn reorder<F: SerializableField>(layer: Layer<F>, mode: &str) -> Layer<F> {
    let segments = layer.delta_segments();
    let mut freq = vec![0usize; segments.len()];
    for &t in layer.delta_tokens() {
        freq[t as usize] += 1;
    }
    let mut order: Vec<_> = (0..segments.len()).collect();
    order.sort_unstable_by_key(|&i| (Reverse(freq[i]), i));
    let mut rank = vec![0; segments.len()];
    for (r, &i) in order.iter().enumerate() {
        rank[i] = r;
    }
    let bucket = |mut r: usize| {
        let mut b = 0;
        while r >= 128 {
            r >>= 7;
            b += 1;
        }
        b
    };
    order.sort_unstable_by(|&a, &b| {
        let primary = if mode.starts_with("bucket") {
            bucket(rank[a]).cmp(&bucket(rank[b]))
        } else {
            std::cmp::Ordering::Equal
        };
        primary
            .then_with(|| {
                if mode.ends_with("suffix") {
                    segments[a].iter().rev().cmp(segments[b].iter().rev())
                } else if mode.ends_with("length") {
                    segments[a]
                        .len()
                        .cmp(&segments[b].len())
                        .then_with(|| segments[a].cmp(&segments[b]))
                } else {
                    segments[a].cmp(&segments[b])
                }
            })
            .then_with(|| a.cmp(&b))
    });
    let mut map = vec![0u32; segments.len()];
    let dict = order
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            map[old] = new as u32;
            segments[old].clone()
        })
        .collect();
    let tokens = layer
        .delta_tokens()
        .iter()
        .map(|&t| map[t as usize])
        .collect();
    Layer::new(
        layer.nw(),
        layer.logw(),
        layer.deltas().to_vec(),
        dict,
        tokens,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use core_proto::TermDelta;
    type F = runtime_algebra::gf2_128::Gf2_128Field;
    #[test]
    fn reorder_preserves_expansion_and_bucket_token_bytes() {
        let segments: Vec<_> = (0..200).map(|i| vec![i % 7, i / 7]).collect();
        let tokens: Vec<_> = (0..200)
            .flat_map(|i| std::iter::repeat_n(i, 201 - i as usize))
            .collect();
        for mode in ["lex", "suffix", "bucketlex", "bucketsuffix", "bucketlength"] {
            let layer = Layer::<F>::new(
                256,
                8,
                (0..200)
                    .map(|i| TermDelta {
                        g: i,
                        h: [i, 0],
                        k_index: 0,
                    })
                    .collect(),
                segments.clone(),
                tokens.clone(),
            );
            let mut before = Vec::new();
            layer.for_each_delta(|d| before.push(*d));
            let out = reorder(layer, mode);
            let mut after = Vec::new();
            out.for_each_delta(|d| after.push(*d));
            assert_eq!(before, after);
            if mode.starts_with("bucket") {
                let bytes = |t: &[u32]| {
                    t.iter()
                        .map(|&i| if i < 128 { 1 } else { 2 })
                        .sum::<usize>()
                };
                assert_eq!(bytes(&tokens), bytes(out.delta_tokens()));
            }
        }
    }
}
