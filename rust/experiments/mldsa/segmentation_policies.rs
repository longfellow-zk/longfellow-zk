// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
//! Offline ordinary-LFC2 segmenters. None changes the executed delta stream.
use core_proto::{Layer, SerializableField};
use std::collections::HashMap;

fn mix(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}

fn symbols<F: SerializableField>(layer: &Layer<F>) -> (Vec<u32>, Vec<u64>) {
    let mut stream = Vec::with_capacity(layer.num_terms());
    layer.for_each_delta_index(|i| stream.push(i));
    // Content-dependent anchors use delta values, not frequency-assigned IDs.
    let hashes = layer
        .deltas()
        .iter()
        .map(|d| {
            [d.g, d.h[0], d.h[1], d.k_index]
                .into_iter()
                .fold(0u64, |h, x| mix(h ^ u64::from(x)))
        })
        .collect();
    (stream, hashes)
}

pub(crate) fn pack<F: SerializableField>(
    layer: &Layer<F>,
    stream: &[u32],
    ends: &[usize],
    stored: bool,
) -> Layer<F> {
    let mut dict = HashMap::<Vec<u32>, u32>::new();
    let mut segments = Vec::new();
    let mut tokens = Vec::new();
    let mut start = 0;
    for &end in ends {
        assert!(end > start && end <= stream.len());
        let slice = &stream[start..end];
        let id = *dict.entry(slice.to_vec()).or_insert_with(|| {
            let id = segments.len() as u32;
            segments.push(slice.to_vec());
            id
        });
        tokens.push(id);
        start = end;
    }
    assert_eq!(start, stream.len());
    let mut freq = vec![0usize; segments.len()];
    for &t in &tokens {
        freq[t as usize] += 1;
    }
    let mut counts = vec![0usize; layer.deltas().len()];
    for (s, &n) in segments.iter().zip(&freq) {
        for &d in s {
            counts[d as usize] += if stored { 1 } else { n };
        }
    }
    let mut order: Vec<_> = (0..counts.len()).collect();
    order.sort_unstable_by_key(|&i| (std::cmp::Reverse(counts[i]), i));
    let mut map = vec![0u32; order.len()];
    let deltas = order
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            map[old] = new as u32;
            layer.deltas()[old]
        })
        .collect();
    for s in &mut segments {
        for d in s {
            *d = map[*d as usize];
        }
    }
    let mut order: Vec<_> = (0..segments.len()).collect();
    order.sort_unstable_by_key(|&i| (std::cmp::Reverse(freq[i]), i));
    let mut map = vec![0; order.len()];
    let segments = order
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            map[old] = new as u32;
            std::mem::take(&mut segments[old])
        })
        .collect();
    for t in &mut tokens {
        *t = map[*t as usize];
    }
    Layer::new(layer.nw(), layer.logw(), deltas, segments, tokens)
}

fn fixed_ends(n: usize, w: usize) -> Vec<usize> {
    (0..n).step_by(w).map(|s| (s + w).min(n)).collect()
}

fn content_ends(stream: &[u32], symbols: &[u64], w: usize) -> Vec<usize> {
    assert!(w.is_power_of_two() && w >= 8);
    let mut ends = Vec::new();
    let mut h = 0u64;
    let mut start = 0;
    // Rolling eight-symbol buzhash. Translation of a repeated delta run does
    // not alter its anchors after the eight-symbol context has synchronized.
    for (i, &x) in stream.iter().enumerate() {
        h = h.rotate_left(1) ^ symbols[x as usize];
        if i >= 8 {
            h ^= symbols[stream[i - 8] as usize].rotate_left(8);
        }
        let len = i + 1 - start;
        if len >= w / 4 && ((h & (w as u64 - 1)) == 0 || len >= 4 * w) {
            ends.push(i + 1);
            start = i + 1;
        }
    }
    if start < stream.len() {
        ends.push(stream.len());
    }
    ends
}

fn macro_ends(stream: &[u32], symbols: &[u64], w: usize) -> Vec<usize> {
    if stream.len() < w {
        return fixed_ends(stream.len(), w);
    }
    const BASE: u64 = 0x100000001b3;
    let pow = (1..w).fold(1u64, |p, _| p.wrapping_mul(BASE));
    let mut hashes = Vec::with_capacity(stream.len() - w + 1);
    let mut h = stream[..w].iter().fold(0u64, |h, &x| {
        h.wrapping_mul(BASE).wrapping_add(symbols[x as usize])
    });
    hashes.push(h);
    for i in w..stream.len() {
        h = h
            .wrapping_sub(symbols[stream[i - w] as usize].wrapping_mul(pow))
            .wrapping_mul(BASE)
            .wrapping_add(symbols[stream[i] as usize]);
        hashes.push(h);
    }
    // Discover at every position, unlike the stock aligned candidate scan.
    // Hashes propose matches only: exact equality below is mandatory.
    let mut candidates = HashMap::<u64, (usize, usize)>::new();
    for (i, &h) in hashes.iter().enumerate() {
        candidates
            .entry(h)
            .and_modify(|c| c.1 += 1)
            .or_insert((i, 1));
    }
    let mut ends = Vec::new();
    let mut i = 0;
    let mut literal_start = 0;
    while i < stream.len() {
        let matched = if i + w <= stream.len() {
            let &(first, count) = candidates.get(&hashes[i]).unwrap();
            count > 1 && stream[first..first + w] == stream[i..i + w]
        } else {
            false
        };
        if matched {
            if literal_start < i {
                ends.push(i);
            }
            i += w;
            ends.push(i);
            literal_start = i;
        } else {
            i += 1;
            if i - literal_start == w {
                ends.push(i);
                literal_start = i;
            }
        }
    }
    if literal_start < i {
        ends.push(i);
    }
    ends
}

pub fn segment<F: SerializableField>(layer: &Layer<F>, policy: &str) -> Layer<F> {
    let (stream, hashes) = symbols(layer);
    let (mode, w) = policy.split_once('_').unwrap();
    let w: usize = w.parse().unwrap();
    assert!(w > 0);
    let ends = match mode {
        "fixed" => fixed_ends(stream.len(), w),
        "cdc" | "cdcstored" => content_ends(&stream, &hashes, w),
        "allphase" => macro_ends(&stream, &hashes, w),
        _ => panic!("unknown segmentation policy {policy}"),
    };
    pack(layer, &stream, &ends, mode == "cdcstored")
}

#[cfg(test)]
mod tests {
    use super::*;
    use core_proto::TermDelta;
    type F = runtime_algebra::gf2_128::Gf2_128Field;
    #[test]
    fn every_policy_preserves_empty_short_shifted_and_repeated_streams() {
        let deltas = (0..80)
            .map(|i| TermDelta {
                g: i,
                h: [i * 2, i * 3],
                k_index: 0,
            })
            .collect();
        let source = Layer::<F>::new(
            256,
            8,
            deltas,
            vec![(0..70).collect(), vec![71, 72, 73], (0..70).collect()],
            vec![0, 1, 2, 0, 2],
        );
        for layer in [&source, &Layer::<F>::new(1, 0, vec![], vec![], vec![])] {
            for policy in [
                "fixed_16",
                "fixed_128",
                "cdc_32",
                "cdc_128",
                "cdcstored_64",
                "allphase_32",
                "allphase_64",
            ] {
                let out = segment(layer, policy);
                let mut before = Vec::new();
                let mut after = Vec::new();
                layer.for_each_delta(|d| before.push(*d));
                out.for_each_delta(|d| after.push(*d));
                assert_eq!(before, after, "{policy}");
                assert_eq!(layer.nw(), out.nw());
                assert!(out.delta_segments().iter().all(|s| !s.is_empty()));
            }
        }
    }
    #[test]
    fn rolling_hash_matches_direct_windows() {
        let symbols: Vec<_> = (0..100).map(mix).collect();
        let stream: Vec<_> = (0..100).collect();
        for w in [16, 32, 64] {
            // With every window unique this must reduce to grouped literals.
            assert_eq!(
                macro_ends(&stream, &symbols, w),
                fixed_ends(stream.len(), w)
            );
        }
        let repeated: Vec<_> = (0..64).chain(90..93).chain(0..64).collect();
        let ends = macro_ends(&repeated, &symbols, 32);
        assert!(ends.contains(&67));
        assert!(ends.contains(&99));
    }
}
