// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
//! Offline binary-pair experiments. The grammar is NEVER serialized: only
//! flattened, actually referenced phrases are emitted as ordinary LFC2 segments.
use core_proto::{Layer, SerializableField};
use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap, HashMap};

#[derive(Clone, Copy)]
struct Phrase {
    start: usize,
    len: usize,
    bytes: usize,
    children: Option<(u32, u32)>,
}

fn uleb(mut n: usize) -> usize {
    let mut b = 1;
    while n >= 128 {
        n >>= 7;
        b += 1;
    }
    b
}

fn score(a: Phrase, b: Phrase, count: usize, cap: usize, gain: bool) -> i64 {
    if count < 2 || a.len + b.len > cap {
        return 0;
    }
    if gain {
        // Conservative flat-storage proxy: two bytes per saved execution token,
        // minus the ENTIRE new phrase body and its length. No credit for parents
        // that might become unused. This is not a zstd or exact byte objective.
        (2 * count) as i64 - (a.bytes + b.bytes + uleb(a.len + b.len)) as i64
    } else {
        count as i64
    }
}

fn initial<F: SerializableField>(
    layer: &Layer<F>,
    delta: bool,
) -> (Vec<u32>, Vec<Phrase>, Vec<u32>) {
    let mut stream = Vec::with_capacity(layer.num_terms());
    layer.for_each_delta_index(|i| stream.push(i));
    if delta {
        let mut phrases: Vec<_> = (0..layer.deltas().len())
            .map(|i| Phrase {
                start: 0,
                len: 1,
                bytes: uleb(i),
                children: None,
            })
            .collect();
        for (i, &s) in stream.iter().enumerate().rev() {
            phrases[s as usize].start = i;
        }
        (stream.clone(), phrases, stream)
    } else {
        let mut phrases: Vec<_> = layer
            .delta_segments()
            .iter()
            .map(|s| Phrase {
                start: 0,
                len: s.len(),
                bytes: s.iter().map(|&d| uleb(d as usize)).sum(),
                children: None,
            })
            .collect();
        let mut offset = 0;
        for &s in layer.delta_tokens() {
            phrases[s as usize].start = offset;
            offset += phrases[s as usize].len;
        }
        (stream, phrases, layer.delta_tokens().to_vec())
    }
}

fn batch(mut tokens: Vec<u32>, phrases: &mut Vec<Phrase>, cap: usize, mode: &str) -> Vec<u32> {
    let gain = mode == "gain";
    let aligned = mode == "aligned";
    loop {
        let mut counts = HashMap::<(u32, u32), usize>::new();
        for i in (0..tokens.len().saturating_sub(1)).step_by(if aligned { 2 } else { 1 }) {
            let (a, b) = (tokens[i], tokens[i + 1]);
            if phrases[a as usize].len + phrases[b as usize].len <= cap {
                *counts.entry((a, b)).or_default() += 1;
            }
        }
        let value = |i: usize| {
            if i + 1 >= tokens.len() || (aligned && i % 2 != 0) {
                return 0;
            }
            let (a, b) = (tokens[i], tokens[i + 1]);
            score(
                phrases[a as usize],
                phrases[b as usize],
                *counts.get(&(a, b)).unwrap_or(&0),
                cap,
                gain,
            )
        };
        // A ranked batch is a local-priority approximation, NOT exact Re-Pair.
        // Count the replacements actually selected, excluding overlaps.
        let mut choices = Vec::new();
        let mut uses = HashMap::<(u32, u32), usize>::new();
        let mut i = 0;
        while i + 1 < tokens.len() {
            let s = value(i);
            if s > 0 && (mode == "left" || aligned || s >= value(i + 1)) {
                choices.push(i);
                *uses.entry((tokens[i], tokens[i + 1])).or_default() += 1;
                i += 2;
            } else {
                i += 1;
            }
        }
        if choices.is_empty() {
            break;
        }
        let mut rules = HashMap::<(u32, u32), u32>::new();
        let mut output = Vec::with_capacity(tokens.len());
        let mut chosen = choices.into_iter().peekable();
        let mut i = 0;
        let mut offset = 0;
        while i < tokens.len() {
            let a = tokens[i];
            if chosen.peek() == Some(&i) {
                chosen.next();
                let b = tokens[i + 1];
                let n = uses[&(a, b)];
                if score(phrases[a as usize], phrases[b as usize], n, cap, gain) > 0 {
                    let id = *rules.entry((a, b)).or_insert_with(|| {
                        let id = phrases.len() as u32;
                        phrases.push(Phrase {
                            start: offset,
                            len: phrases[a as usize].len + phrases[b as usize].len,
                            bytes: phrases[a as usize].bytes + phrases[b as usize].bytes,
                            children: Some((a, b)),
                        });
                        id
                    });
                    output.push(id);
                    offset += phrases[id as usize].len;
                    i += 2;
                    continue;
                }
            }
            output.push(a);
            offset += phrases[a as usize].len;
            i += 1;
        }
        if output.len() == tokens.len() {
            break;
        }
        tokens = output;
    }
    tokens
}

type Pair = (u32, u32);
fn change(
    occ: &mut HashMap<Pair, BTreeSet<usize>>,
    dirty: &mut Vec<Pair>,
    pair: Pair,
    pos: usize,
    add: bool,
) {
    let set = occ.entry(pair).or_default();
    if add {
        assert!(set.insert(pos));
    } else {
        assert!(set.remove(&pos));
    }
    dirty.push(pair);
}

/// Exact highest-current-frequency pair selection (overlapping adjacency counts),
/// with deterministic left-to-right nonoverlapping replacement. Length bounded.
fn repair(mut tokens: Vec<u32>, phrases: &mut Vec<Phrase>, cap: usize, gain: bool) -> Vec<u32> {
    const NONE: usize = usize::MAX;
    let n = tokens.len();
    if n < 2 {
        return tokens;
    }
    let mut prev: Vec<_> = (0..n).map(|i| if i == 0 { NONE } else { i - 1 }).collect();
    let mut next: Vec<_> = (0..n)
        .map(|i| if i + 1 == n { NONE } else { i + 1 })
        .collect();
    let mut starts = Vec::with_capacity(n);
    let mut offset = 0;
    for &t in &tokens {
        starts.push(offset);
        offset += phrases[t as usize].len;
    }
    let mut live = vec![true; n];
    let mut occ = HashMap::<Pair, BTreeSet<usize>>::new();
    for i in 0..n - 1 {
        occ.entry((tokens[i], tokens[i + 1])).or_default().insert(i);
    }
    let mut heap = BinaryHeap::new();
    for (&(a, b), set) in &occ {
        let s = score(
            phrases[a as usize],
            phrases[b as usize],
            set.len(),
            cap,
            gain,
        );
        if s > 0 {
            heap.push((s, Reverse((a, b))));
        }
    }
    while let Some((old, Reverse((a, b)))) = heap.pop() {
        let count = occ[&(a, b)].len();
        if old != score(phrases[a as usize], phrases[b as usize], count, cap, gain) {
            continue;
        }
        let mut last_right = NONE;
        let positions: Vec<_> = occ[&(a, b)]
            .iter()
            .copied()
            .filter(|&p| {
                if p == last_right {
                    false
                } else {
                    last_right = next[p];
                    true
                }
            })
            .collect();
        if score(
            phrases[a as usize],
            phrases[b as usize],
            positions.len(),
            cap,
            gain,
        ) <= 0
        {
            continue;
        }
        let id = phrases.len() as u32;
        phrases.push(Phrase {
            start: starts[positions[0]],
            len: phrases[a as usize].len + phrases[b as usize].len,
            bytes: phrases[a as usize].bytes + phrases[b as usize].bytes,
            children: Some((a, b)),
        });
        let mut dirty = Vec::new();
        for p in positions {
            let q = next[p];
            assert!(live[p] && q != NONE && live[q] && tokens[p] == a && tokens[q] == b);
            let l = prev[p];
            let r = next[q];
            if l != NONE {
                change(&mut occ, &mut dirty, (tokens[l], a), l, false);
            }
            change(&mut occ, &mut dirty, (a, b), p, false);
            if r != NONE {
                change(&mut occ, &mut dirty, (b, tokens[r]), q, false);
            }
            tokens[p] = id;
            next[p] = r;
            live[q] = false;
            if r != NONE {
                prev[r] = p;
            }
            if l != NONE {
                change(&mut occ, &mut dirty, (tokens[l], id), l, true);
            }
            if r != NONE {
                change(&mut occ, &mut dirty, (id, tokens[r]), p, true);
            }
        }
        dirty.sort_unstable();
        dirty.dedup();
        for (a, b) in dirty {
            let s = score(
                phrases[a as usize],
                phrases[b as usize],
                occ[&(a, b)].len(),
                cap,
                gain,
            );
            if s > 0 {
                heap.push((s, Reverse((a, b))));
            }
        }
    }
    tokens
        .into_iter()
        .zip(live)
        .filter_map(|(t, l)| l.then_some(t))
        .collect()
}

/// Choose a cut through the learned binary grammar, charging a flat body once
/// amortized over all its grammar occurrences. Counts are an estimate: choosing
/// an ancestor can hide some descendant uses. This is not globally optimal.
fn prune(tokens: Vec<u32>, phrases: &[Phrase]) -> Vec<u32> {
    let mut counts = vec![0usize; phrases.len()];
    for &t in &tokens {
        counts[t as usize] += 1;
    }
    for i in (0..phrases.len()).rev() {
        if let Some((a, b)) = phrases[i].children {
            counts[a as usize] += counts[i];
            counts[b as usize] += counts[i];
        }
    }
    let mut cost = vec![0f64; phrases.len()];
    let mut split = vec![false; phrases.len()];
    for (i, p) in phrases.iter().enumerate() {
        cost[i] = 2.0 + (p.bytes + uleb(p.len)) as f64 / counts[i].max(1) as f64;
        if let Some((a, b)) = p.children {
            let c = cost[a as usize] + cost[b as usize];
            if c < cost[i] {
                cost[i] = c;
                split[i] = true;
            }
        }
    }
    let mut out = Vec::new();
    let mut stack: Vec<_> = tokens.into_iter().rev().collect();
    while let Some(t) = stack.pop() {
        if split[t as usize] {
            let (a, b) = phrases[t as usize].children.unwrap();
            stack.push(b);
            stack.push(a);
        } else {
            out.push(t);
        }
    }
    out
}

fn ends(tokens: &[u32], phrases: &[Phrase], group: bool) -> Vec<usize> {
    let mut counts = vec![0usize; phrases.len()];
    for &t in tokens {
        counts[t as usize] += 1;
    }
    let mut ends = Vec::new();
    let mut offset = 0;
    let mut literal = 0;
    for &t in tokens {
        let p = phrases[t as usize];
        if group && (p.len == 1 || counts[t as usize] == 1) && p.len <= 64 {
            if literal + p.len > 64 {
                ends.push(offset);
                literal = 0;
            }
            literal += p.len;
            offset += p.len;
        } else {
            if literal > 0 {
                ends.push(offset);
                literal = 0;
            }
            offset += p.len;
            ends.push(offset);
        }
    }
    if literal > 0 {
        ends.push(offset);
    }
    ends
}

fn lz78(stream: &[u32], cap: usize) -> Vec<usize> {
    let mut trie = HashMap::<(usize, u32), usize>::new();
    let mut ends = Vec::new();
    let mut i = 0;
    while i < stream.len() {
        let start = i;
        let mut node = 0;
        while i < stream.len() && i - start < cap {
            let key = (node, stream[i]);
            i += 1;
            if let Some(&child) = trie.get(&key) {
                node = child;
            } else {
                let id = trie.len() + 1;
                trie.insert(key, id);
                break;
            }
        }
        ends.push(i);
    }
    ends
}

/// policy: delta/seed + left/rank/aligned/gain/repair/repairgain + cap,
/// optionally + raw (do not group singleton/one-use final phrases).
pub fn segment<F: SerializableField>(layer: &Layer<F>, policy: &str) -> Layer<F> {
    let parts: Vec<_> = policy.split('_').collect();
    if parts[0] == "lz78" {
        let cap: usize = parts[1].parse().unwrap();
        assert!(cap > 0);
        let mut stream = Vec::new();
        layer.for_each_delta_index(|d| stream.push(d));
        return super::policies::pack(layer, &stream, &lz78(&stream, cap), false);
    }
    assert!(matches!(parts[0], "delta" | "seed"));
    let (stream, mut phrases, tokens) = initial(layer, parts[0] == "delta");
    let cap = parts[2].parse().unwrap();
    assert!(cap > 0);
    assert!(parts.len() == 3 || (parts.len() == 4 && matches!(parts[3], "raw" | "prune")));
    let tokens = match parts[1] {
        "repair" | "repairgain" => repair(tokens, &mut phrases, cap, parts[1] == "repairgain"),
        "left" | "rank" | "aligned" | "gain" => batch(tokens, &mut phrases, cap, parts[1]),
        _ => panic!("unknown pair policy {policy}"),
    };
    let tokens = if parts.get(3) == Some(&"prune") {
        prune(tokens, &phrases)
    } else {
        tokens
    };
    // Check the grammar's expansion itself before discarding it; pack() alone
    // would only check that the chosen boundaries partition the original stream.
    let mut i = 0;
    for &t in &tokens {
        let p = phrases[t as usize];
        assert_eq!(&stream[i..i + p.len], &stream[p.start..p.start + p.len]);
        i += p.len;
    }
    assert_eq!(i, stream.len());
    super::policies::pack(
        layer,
        &stream,
        &ends(&tokens, &phrases, parts.get(3) != Some(&"raw")),
        false,
    )
}

/// Pair parsing over an arbitrary integer alphabet, for the three-level format
/// experiment. Returned phrase bodies refer to the ORIGINAL symbols, not rules.
pub fn parse_symbols(
    stream: &[u32],
    cap: usize,
    pruned: bool,
    group: bool,
) -> (Vec<Vec<u32>>, Vec<u32>) {
    assert!(cap > 0);
    let n = stream.iter().copied().max().map_or(0, |n| n as usize + 1);
    let mut phrases: Vec<_> = (0..n)
        .map(|i| Phrase {
            start: 0,
            len: 1,
            bytes: uleb(i),
            children: None,
        })
        .collect();
    for (i, &t) in stream.iter().enumerate().rev() {
        phrases[t as usize].start = i;
    }
    let tokens = repair(stream.to_vec(), &mut phrases, cap, false);
    let tokens = if pruned {
        prune(tokens, &phrases)
    } else {
        tokens
    };
    let mut offset = 0;
    for &t in &tokens {
        let p = phrases[t as usize];
        assert_eq!(
            &stream[offset..offset + p.len],
            &stream[p.start..p.start + p.len]
        );
        offset += p.len;
    }
    assert_eq!(offset, stream.len());
    let mut dict = Vec::new();
    let mut index = HashMap::<Vec<u32>, u32>::new();
    let mut out = Vec::new();
    let mut start = 0;
    for end in ends(&tokens, &phrases, group) {
        let s = &stream[start..end];
        let id = *index.entry(s.to_vec()).or_insert_with(|| {
            let id = dict.len() as u32;
            dict.push(s.to_vec());
            id
        });
        out.push(id);
        start = end;
    }
    (dict, out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core_proto::TermDelta;
    type F = runtime_algebra::gf2_128::Gf2_128Field;
    #[test]
    fn heap_repair_matches_slow_recount_reference() {
        fn reference(mut ts: Vec<u32>, ps: &mut Vec<Phrase>, cap: usize, gain: bool) -> Vec<u32> {
            loop {
                let mut counts = HashMap::<Pair, usize>::new();
                for w in ts.windows(2) {
                    *counts.entry((w[0], w[1])).or_default() += 1;
                }
                let mut candidates: Vec<_> = counts
                    .into_iter()
                    .map(|((a, b), n)| {
                        (
                            score(ps[a as usize], ps[b as usize], n, cap, gain),
                            Reverse((a, b)),
                        )
                    })
                    .filter(|(s, _)| *s > 0)
                    .collect();
                candidates.sort_unstable();
                let mut selected = None;
                while let Some((_, Reverse((a, b)))) = candidates.pop() {
                    let mut i = 0;
                    let mut uses = 0;
                    while i + 1 < ts.len() {
                        if ts[i] == a && ts[i + 1] == b {
                            uses += 1;
                            i += 2;
                        } else {
                            i += 1;
                        }
                    }
                    if score(ps[a as usize], ps[b as usize], uses, cap, gain) > 0 {
                        selected = Some((a, b));
                        break;
                    }
                }
                let Some((a, b)) = selected else {
                    break;
                };
                let id = ps.len() as u32;
                ps.push(Phrase {
                    start: 0,
                    len: ps[a as usize].len + ps[b as usize].len,
                    bytes: ps[a as usize].bytes + ps[b as usize].bytes,
                    children: Some((a, b)),
                });
                let mut out = Vec::new();
                let mut i = 0;
                while i < ts.len() {
                    if i + 1 < ts.len() && ts[i] == a && ts[i + 1] == b {
                        out.push(id);
                        i += 2;
                    } else {
                        out.push(ts[i]);
                        i += 1;
                    }
                }
                ts = out;
            }
            ts
        }
        let mut state = 123u32;
        for n in [0, 1, 3, 10, 100, 1001] {
            let random: Vec<_> = (0..n)
                .map(|_| {
                    state = state.wrapping_mul(1664525).wrapping_add(1013904223);
                    (state >> 24) % 6
                })
                .collect();
            for tokens in [random, vec![0; n], (0..n).map(|i| (i % 2) as u32).collect()] {
                for cap in [8, 32, 128] {
                    for gain in [false, true] {
                        let ps = vec![
                            Phrase {
                                start: 0,
                                len: 1,
                                bytes: 1,
                                children: None
                            };
                            6
                        ];
                        assert_eq!(
                            repair(tokens.clone(), &mut ps.clone(), cap, gain),
                            reference(tokens.clone(), &mut ps.clone(), cap, gain)
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn pairs_preserve_and_are_deterministic() {
        let mut inputs = vec![
            vec![],
            vec![0],
            vec![0; 513],
            vec![0, 1, 0, 1, 0],
            (0..64).collect(),
        ];
        inputs.push((0..70).flat_map(|i| (0..31).chain([i % 3])).collect());
        let mut state = 123u32;
        for n in [5, 20, 100, 1000] {
            inputs.push(
                (0..n)
                    .map(|_| {
                        state = state.wrapping_mul(1664525).wrapping_add(1013904223);
                        state % 7
                    })
                    .collect(),
            );
        }
        for stream in inputs {
            let layer = Layer::<F>::new(
                128,
                7,
                (0..64)
                    .map(|i| TermDelta {
                        g: i,
                        h: [0u32.wrapping_sub(i), i * 2],
                        k_index: i % 3,
                    })
                    .collect(),
                if stream.is_empty() {
                    vec![]
                } else {
                    vec![stream.clone()]
                },
                if stream.is_empty() { vec![] } else { vec![0] },
            );
            let seeded = super::super::policies::pack(
                &layer,
                &stream,
                &(0..stream.len())
                    .step_by(3)
                    .map(|i| (i + 3).min(stream.len()))
                    .collect::<Vec<_>>(),
                false,
            );
            for seed in ["delta", "seed"] {
                for strategy in ["left", "rank", "aligned", "gain", "repair", "repairgain"] {
                    for cap in [4, 32, 128] {
                        for suffix in ["", "_raw", "_prune"] {
                            let policy = format!("{seed}_{strategy}_{cap}{suffix}");
                            let a = segment(&seeded, &policy);
                            let b = segment(&seeded, &policy);
                            assert_eq!(a.delta_segments(), b.delta_segments());
                            assert_eq!(a.delta_tokens(), b.delta_tokens());
                            let mut expected = Vec::new();
                            layer.for_each_delta(|d| expected.push(*d));
                            let mut actual = Vec::new();
                            a.for_each_delta(|d| actual.push(*d));
                            assert_eq!(expected, actual, "{policy}");
                        }
                    }
                }
            }
            for cap in [4, 32, 128] {
                let a = segment(&layer, &format!("lz78_{cap}"));
                let mut actual = Vec::new();
                a.for_each_delta(|d| actual.push(*d));
                let expected: Vec<_> = stream.iter().map(|&d| layer.deltas()[d as usize]).collect();
                assert_eq!(expected, actual);
            }
        }
    }
}
