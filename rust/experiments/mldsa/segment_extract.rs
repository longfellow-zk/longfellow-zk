// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
//! Flat prefix/suffix factoring: split existing dictionary bodies at shared trie
//! branches. Both children remain ordinary segments; no recursive references.
use core_proto::{Layer, SerializableField};

fn cuts(segments: &[Vec<u32>], min: usize, reverse: bool) -> Vec<Vec<usize>> {
    assert!(min > 0);
    let mut out: Vec<Vec<usize>> = segments.iter().map(|s| vec![s.len()]).collect();
    let at = |i: usize, p: usize| {
        if reverse {
            segments[i][segments[i].len() - 1 - p]
        } else {
            segments[i][p]
        }
    };
    let mut order: Vec<_> = (0..segments.len())
        .filter(|&i| !segments[i].is_empty())
        .collect();
    order.sort_unstable_by(|&a, &b| {
        if reverse {
            segments[a].iter().rev().cmp(segments[b].iter().rev())
        } else {
            segments[a].cmp(&segments[b])
        }
    });
    // (interval, already-known prefix depth, last emitted cut depth).
    let mut stack = vec![(0, order.len(), 0, 0)];
    while let Some((lo, hi, mut depth, mut emitted)) = stack.pop() {
        if hi - lo < 2 {
            continue;
        }
        let a = order[lo];
        let b = order[hi - 1];
        while depth < segments[a].len().min(segments[b].len()) && at(a, depth) == at(b, depth) {
            depth += 1;
        }
        if depth - emitted >= min {
            for &id in &order[lo..hi] {
                let cut = if reverse {
                    segments[id].len() - depth
                } else {
                    depth
                };
                if cut > 0 && cut < segments[id].len() {
                    out[id].push(cut);
                }
            }
            emitted = depth;
        }
        let mut start = lo;
        while start < hi {
            if segments[order[start]].len() == depth {
                start += 1;
                continue;
            }
            let symbol = at(order[start], depth);
            let mut end = start + 1;
            while end < hi && segments[order[end]].len() > depth && at(order[end], depth) == symbol
            {
                end += 1;
            }
            stack.push((start, end, depth + 1, emitted));
            start = end;
        }
    }
    for c in &mut out {
        c.sort_unstable();
        c.dedup();
    }
    out
}

fn one<F: SerializableField>(layer: Layer<F>, min: usize, reverse: bool) -> Layer<F> {
    let cuts = cuts(layer.delta_segments(), min, reverse);
    let mut stream = Vec::with_capacity(layer.num_terms());
    let mut ends = Vec::new();
    for &t in layer.delta_tokens() {
        let offset = stream.len();
        stream.extend_from_slice(&layer.delta_segments()[t as usize]);
        ends.extend(cuts[t as usize].iter().map(|&c| offset + c));
    }
    super::policies::pack(&layer, &stream, &ends, false)
}

pub fn extract<F: SerializableField>(layer: Layer<F>, mode: &str) -> Layer<F> {
    let split = mode.find(|c: char| c.is_ascii_digit()).unwrap();
    let (kind, n) = mode.split_at(split);
    let n = n.parse().unwrap();
    match kind {
        "prefix" => one(layer, n, false),
        "suffix" => one(layer, n, true),
        "both" => one(one(layer, n, false), n, true),
        _ => panic!("unknown factor mode {mode}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core_proto::TermDelta;
    type F = runtime_algebra::gf2_128::Gf2_128Field;
    #[test]
    fn trie_shares_nested_prefixes_and_suffixes_exactly() {
        let segments = vec![
            vec![0, 1, 2, 3],
            vec![0, 1, 2, 4],
            vec![0, 1, 5, 4],
            vec![0, 1],
        ];
        assert_eq!(
            cuts(&segments, 2, false),
            vec![vec![2, 4], vec![2, 4], vec![2, 4], vec![2]]
        );
        assert_eq!(
            cuts(&segments, 1, false),
            vec![vec![2, 3, 4], vec![2, 3, 4], vec![2, 4], vec![2]]
        );
        for mode in ["prefix1", "prefix2", "suffix1", "both1", "both8"] {
            let layer = Layer::<F>::new(
                8,
                3,
                (0..8)
                    .map(|g| TermDelta {
                        g,
                        h: [0, 0],
                        k_index: 0,
                    })
                    .collect(),
                segments.clone(),
                vec![0, 1, 2, 3, 0, 2],
            );
            let mut before = Vec::new();
            layer.for_each_delta(|d| before.push(*d));
            let out = extract(layer, mode);
            let mut after = Vec::new();
            out.for_each_delta(|d| after.push(*d));
            assert_eq!(before, after);
        }
    }
}
