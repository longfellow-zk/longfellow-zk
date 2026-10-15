// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
//! Trusted offline L3E1 experiment: deltas -> base phrases -> upper phrases.
//! Not a production format or reader. No arbitrary-depth grammar references.
#[allow(dead_code)]
#[path = "../../../experiments/mldsa/pair_segments.rs"]
mod pairs;
#[allow(dead_code)]
#[path = "../../../experiments/mldsa/segmentation_policies.rs"]
mod policies;
use core_proto::{FieldID, SerializableField};
use std::{cmp::Reverse, path::PathBuf, time::Instant};

#[derive(Clone)]
struct Level {
    // Unmodified width and delta-table bytes, including counts.
    metadata: Vec<u8>,
    nd: usize,
    lower: Vec<Vec<u32>>,
    upper: Vec<Vec<u32>>,
    roots: Vec<u32>,
}
#[derive(Clone)]
struct File {
    prefix: Vec<u8>,
    levels: Vec<Level>,
    id: [u8; 32],
}
struct Read<'a> {
    data: &'a [u8],
    pos: usize,
}
impl Read<'_> {
    fn n(&mut self) -> usize {
        let mut n = 0usize;
        for shift in (0..28).step_by(7) {
            let b = self.data[self.pos];
            self.pos += 1;
            n |= usize::from(b & 127) << shift;
            if b < 128 {
                return n;
            }
        }
        panic!("invalid max-four-byte ULEB");
    }
    fn list(&mut self) -> Vec<u32> {
        let n = self.n();
        (0..n).map(|_| self.n() as u32).collect()
    }
    fn dict(&mut self) -> Vec<Vec<u32>> {
        let n = self.n();
        (0..n).map(|_| self.list()).collect()
    }
}
fn put(out: &mut Vec<u8>, mut n: usize) {
    assert!(n < 1 << 28);
    while n >= 128 {
        out.push((n as u8 & 127) | 128);
        n >>= 7;
    }
    out.push(n as u8);
}
fn list(out: &mut Vec<u8>, v: &[u32]) {
    put(out, v.len());
    for &i in v {
        put(out, i as usize);
    }
}
fn dict(out: &mut Vec<u8>, v: &[Vec<u32>]) {
    put(out, v.len());
    for s in v {
        list(out, s);
    }
}

fn read(data: &[u8], field_bytes: usize, three: bool) -> File {
    assert_eq!(&data[..4], if three { b"L3E1" } else { b"LFC2" });
    let mut r = Read { data, pos: 4 };
    for _ in 0..6 {
        r.n();
    }
    let nl = r.n();
    let nc = r.n();
    r.pos += nc * field_bytes;
    let prefix = data[..r.pos].to_vec();
    let mut levels = Vec::new();
    for _ in 0..nl {
        let start = r.pos;
        r.n();
        r.n();
        let nd = r.n();
        for _ in 0..nd * 4 {
            r.n();
        }
        let metadata = data[start..r.pos].to_vec();
        let lower = r.dict();
        let upper = if three {
            r.dict()
        } else {
            (0..lower.len()).map(|i| vec![i as u32]).collect()
        };
        let roots = r.list();
        assert!(lower
            .iter()
            .all(|s| !s.is_empty() && s.iter().all(|&d| (d as usize) < nd)));
        assert!(upper
            .iter()
            .all(|s| !s.is_empty() && s.iter().all(|&d| (d as usize) < lower.len())));
        assert!(roots.iter().all(|&d| (d as usize) < upper.len()));
        levels.push(Level {
            metadata,
            nd,
            lower,
            upper,
            roots,
        });
    }
    assert_eq!(r.pos + 32, data.len());
    File {
        prefix,
        levels,
        id: data[r.pos..].try_into().unwrap(),
    }
}
fn write(c: &File, three: bool) -> Vec<u8> {
    let mut out = c.prefix.clone();
    out[..4].copy_from_slice(if three { b"L3E1" } else { b"LFC2" });
    for l in &c.levels {
        out.extend_from_slice(&l.metadata);
        if three {
            dict(&mut out, &l.lower);
            dict(&mut out, &l.upper);
        } else {
            let expanded: Vec<Vec<u32>> = l
                .upper
                .iter()
                .map(|s| {
                    s.iter()
                        .flat_map(|&t| l.lower[t as usize].iter().copied())
                        .collect()
                })
                .collect();
            dict(&mut out, &expanded);
        }
        list(&mut out, &l.roots);
    }
    out.extend_from_slice(&c.id);
    out
}

fn normalize(l: &mut Level, suffix: bool) {
    // Remove dead bodies and rank reference IDs by actual expanded use count.
    let mut uf = vec![0usize; l.upper.len()];
    for &t in &l.roots {
        uf[t as usize] += 1;
    }
    let mut lf = vec![0usize; l.lower.len()];
    for (s, &n) in l.upper.iter().zip(&uf) {
        for &t in s {
            lf[t as usize] += n;
        }
    }
    fn order(dict: &[Vec<u32>], freq: &[usize], suffix: bool) -> Vec<usize> {
        let mut ids: Vec<_> = (0..dict.len()).filter(|&i| freq[i] > 0).collect();
        ids.sort_unstable_by_key(|&i| (Reverse(freq[i]), i));
        if suffix {
            let mut ranks = vec![0; dict.len()];
            for (r, &i) in ids.iter().enumerate() {
                ranks[i] = r;
            }
            let width = |mut n: usize| {
                let mut b = 1;
                while n >= 128 {
                    b += 1;
                    n >>= 7;
                }
                b
            };
            ids.sort_unstable_by(|&a, &b| {
                width(ranks[a])
                    .cmp(&width(ranks[b]))
                    .then_with(|| dict[a].iter().rev().cmp(dict[b].iter().rev()))
                    .then_with(|| a.cmp(&b))
            });
        }
        ids
    }
    let ids = order(&l.lower, &lf, suffix);
    let mut map = vec![u32::MAX; l.lower.len()];
    l.lower = ids
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            map[old] = new as u32;
            std::mem::take(&mut l.lower[old])
        })
        .collect();
    for (s, &n) in l.upper.iter_mut().zip(&uf) {
        if n > 0 {
            for t in s {
                *t = map[*t as usize];
                assert_ne!(*t, u32::MAX);
            }
        }
    }
    let ids = order(&l.upper, &uf, suffix);
    let mut map = vec![u32::MAX; l.upper.len()];
    l.upper = ids
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            map[old] = new as u32;
            std::mem::take(&mut l.upper[old])
        })
        .collect();
    for t in &mut l.roots {
        *t = map[*t as usize];
        assert_ne!(*t, u32::MAX);
    }
}

fn build(source: &File, policy: &str) -> File {
    let parts: Vec<_> = policy.split('_').collect();
    let cap: usize = parts[1].parse().unwrap();
    let pruned = parts.contains(&"prune");
    let suffix = parts.contains(&"suffix");
    let mut out = source.clone();
    for l in &mut out.levels {
        match parts[0] {
            "top" => {
                // Old lower bodies are retained, new upper bodies contain old IDs.
                let (upper, roots) = pairs::parse_symbols(&l.roots, cap, pruned, true);
                l.upper = upper;
                l.roots = roots;
            }
            "factor" => {
                // Learn shared bases across STORED dictionary bodies, not their
                // expansions. Unique barriers forbid rules crossing body edges.
                let mut stream = Vec::new();
                for (i, s) in l.lower.iter().enumerate() {
                    stream.extend_from_slice(s);
                    stream.push((l.nd + i) as u32);
                }
                let (phrases, tokens) = pairs::parse_symbols(&stream, cap, pruned, false);
                let mut lower = Vec::new();
                let mut map = vec![u32::MAX; phrases.len()];
                for (i, p) in phrases.iter().enumerate() {
                    if p.iter().any(|&d| d as usize >= l.nd) {
                        assert_eq!(p.len(), 1);
                    } else {
                        map[i] = lower.len() as u32;
                        lower.push(p.clone());
                    }
                }
                let mut upper = Vec::new();
                let mut current = Vec::new();
                for t in tokens {
                    if map[t as usize] == u32::MAX {
                        assert_eq!(phrases[t as usize], vec![(l.nd + upper.len()) as u32]);
                        upper.push(std::mem::take(&mut current));
                    } else {
                        current.push(map[t as usize]);
                    }
                }
                assert!(current.is_empty());
                assert_eq!(upper.len(), l.lower.len());
                for (a, b) in l.lower.iter().zip(&upper) {
                    assert!(a
                        .iter()
                        .copied()
                        .eq(b.iter().flat_map(|&t| lower[t as usize].iter().copied())));
                }
                l.lower = lower;
                l.upper = upper;
            }
            "two" => {
                // Two independent bounded Re-Pair passes on the execution stream.
                let stream: Vec<_> = l
                    .roots
                    .iter()
                    .flat_map(|&t| l.lower[t as usize].iter().copied())
                    .collect();
                let (lower, mid) = pairs::parse_symbols(&stream, cap, pruned, true);
                let upper_cap = parts[2].parse().unwrap();
                let (upper, roots) = pairs::parse_symbols(&mid, upper_cap, pruned, true);
                l.lower = lower;
                l.upper = upper;
                l.roots = roots;
            }
            _ => panic!("unknown policy {policy}"),
        }
        normalize(l, suffix);
    }
    out
}

fn checksum(c: &File) -> u64 {
    let mut sum = 0u64;
    for l in &c.levels {
        for &r in &l.roots {
            for &s in &l.upper[r as usize] {
                for &d in &l.lower[s as usize] {
                    sum = sum.wrapping_mul(31).wrapping_add(u64::from(d));
                }
            }
        }
    }
    sum
}

fn run<F: SerializableField + core_algebra::AlgebraicField + Clone>(
    name: &str,
    f: &F,
    field: FieldID,
    width: usize,
) {
    let input = std::fs::read(std::env::var("ORDER_INPUT_CIRCUIT").unwrap()).unwrap();
    let reader = core_proto::reader::CircuitReader::new(f, field);
    let (original, tail) = reader.from_bytes(&input, true).unwrap();
    assert!(tail.is_empty());
    let source = read(&input, width, false);
    assert_eq!(write(&source, false), input);
    let source_sum = checksum(&source);
    let folder = PathBuf::from(std::env::var("THREE_OUTPUT").unwrap());
    std::fs::create_dir_all(&folder).unwrap();
    let seed = std::env::var("THREE_SEED").unwrap();
    println!(
        "THREE_BASE dataset={name} seed={seed} raw={} z16={} z22={}",
        input.len(),
        zstd::bulk::compress(&input, 16).unwrap().len(),
        zstd::bulk::compress(&input, 22).unwrap().len()
    );
    let mut checksum_flat = 0u64;
    let start = Instant::now();
    for _ in 0..5 {
        let mut sum = 0u64;
        for l in &original.raw.layers {
            l.for_each_delta_index(|d| sum = sum.wrapping_mul(31).wrapping_add(u64::from(d)));
        }
        checksum_flat = std::hint::black_box(sum);
    }
    let flat_scan_ms = start.elapsed().as_secs_f64() * 200.;
    assert_eq!(checksum_flat, source_sum);
    for policy in std::env::var("THREE_POLICIES").unwrap().split(',') {
        let start = Instant::now();
        let result = build(&source, policy);
        let segment_ms = start.elapsed().as_secs_f64() * 1000.;
        let bytes = write(&result, true);
        let start = Instant::now();
        let decoded = read(&bytes, width, true);
        let decode_ms = start.elapsed().as_secs_f64() * 1000.;
        assert_eq!(write(&decoded, true), bytes);
        assert_eq!(checksum(&decoded), source_sum);
        let flattened = write(&decoded, false);
        let (c, tail) = reader.from_bytes(&flattened, true).unwrap();
        assert!(tail.is_empty());
        assert_eq!(c.id, original.id);
        for (a, b) in original.raw.layers.iter().zip(&c.raw.layers) {
            let mut expected = Vec::new();
            a.for_each_delta(|d| expected.push(*d));
            let mut i = 0;
            b.for_each_delta(|d| {
                assert_eq!(*d, expected[i]);
                i += 1;
            });
            assert_eq!(i, expected.len());
        }
        let start = Instant::now();
        for _ in 0..5 {
            assert_eq!(std::hint::black_box(checksum(&decoded)), source_sum);
        }
        let scan_ms = start.elapsed().as_secs_f64() * 200.;
        let raw = bytes.len();
        let z16 = zstd::bulk::compress(&bytes, 16).unwrap().len();
        let z22 = zstd::bulk::compress(&bytes, 22).unwrap().len();
        let lower_entries: usize = decoded
            .levels
            .iter()
            .flat_map(|l| &l.lower)
            .map(Vec::len)
            .sum();
        let upper_entries: usize = decoded
            .levels
            .iter()
            .flat_map(|l| &l.upper)
            .map(Vec::len)
            .sum();
        let roots: usize = decoded.levels.iter().map(|l| l.roots.len()).sum();
        println!("THREE_SIZE dataset={name} seed={seed} policy={policy} raw={raw} z16={z16} z22={z22} lower_entries={lower_entries} upper_entries={upper_entries} roots={roots} segment_ms={segment_ms:.3} decode_ms={decode_ms:.3} scan_ms={scan_ms:.3} flat_scan_ms={flat_scan_ms:.3} exact=true");
        std::fs::write(folder.join(format!("{policy}.l3e")), bytes).unwrap();
        std::fs::write(folder.join(format!("{policy}.lfc2")), flattened).unwrap();
    }
}

#[test]
#[ignore = "offline three-level size experiment"]
fn three_level_sweep() {
    let name = std::env::var("ORDER_DATASET").unwrap();
    match name.as_str() {
        "mldsa44" | "mldsa65" => run(
            &name,
            &circuits_experimental::mldsa::algebra::RuntimeFp24Ext6::new(),
            FieldID::None,
            18,
        ),
        "mdoc_sig" => run(
            &name,
            &runtime_algebra::p256::P256Field::new(),
            FieldID::P256,
            32,
        ),
        "mdoc_hash2" => run(
            &name,
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            FieldID::Gf2_128,
            16,
        ),
        _ => panic!("unknown dataset"),
    }
}

#[test]
#[ignore = "actual archive of experimental three-level payloads"]
fn three_level_archive() {
    let mut b = core_proto::archive::CircuitArchiveBuilder::new();
    b.set_circuit_version(mdoc_zk_circuits::CURRENT_VERSION as u32);
    for (name, var) in [("sig", "ORDER_SIG"), ("hash", "ORDER_HASH")] {
        let data = std::fs::read(std::env::var(var).unwrap()).unwrap();
        let id = data[data.len() - 32..].try_into().unwrap();
        b.add_entry(name, id, data);
    }
    let raw = b.build().to_bytes();
    println!(
        "THREE_ARCHIVE raw={} z16={} z22={}",
        raw.len(),
        zstd::encode_all(&raw[..], 16).unwrap().len(),
        zstd::encode_all(&raw[..], 22).unwrap().len()
    );
}

#[test]
fn three_levels_preserve_boundaries_and_empty_layers() {
    for lower in [
        vec![],
        vec![
            vec![0; 100],
            vec![0, 1, 2, 0, 1, 2],
            vec![1, 2],
            vec![0, 1, 2, 0, 1, 3],
        ],
    ] {
        let source = File {
            prefix: vec![0;4],
            id: [0; 32],
            levels: vec![Level {
                metadata: vec![],
                nd: 4,
                roots: (0..lower.len() as u32)
                    .cycle()
                    .take(lower.len() * 4)
                    .collect(),
                upper: (0..lower.len()).map(|i| vec![i as u32]).collect(),
                lower,
            }],
        };
        let original = checksum(&source);
        for policy in [
            "top_8",
            "top_64_prune",
            "factor_8",
            "factor_32_prune_suffix",
            "two_8_8",
            "two_8_32_prune_suffix",
        ] {
            let out = build(&source, policy);
            assert_eq!(checksum(&out), original);
            assert_eq!(write(&out, true), write(&build(&source, policy), true));
        }
    }
}
