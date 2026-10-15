// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Offline LFR1 experiment. No production format or circuit-ID changes.
//! A reference applies three wrapping coordinate corrections to the FIRST delta
//! of a segment. Applying them to every delta is a separate, explicitly tagged
//! control: that models an affine ramp, not translation of absolute term wires.
//! Coefficients are never differenced or corrected. The adapter expands only
//! dictionaries back to ordinary compact LFC2, never an array of all terms.

use core_proto::layer::TermDelta;
use core_proto::uleb::{read_uleb128_max4, serialize_uleb128_max4};
use std::collections::{HashMap, HashSet};

const LIMIT: usize = 40_000_000;
fn put(b: &mut Vec<u8>, n: usize) {
    serialize_uleb128_max4(b, n);
}
fn get(b: &mut &[u8]) -> Result<usize, String> {
    read_uleb128_max4(b)
}
fn take<'a>(b: &mut &'a [u8], n: usize) -> Result<&'a [u8], String> {
    if n > b.len() {
        return Err("truncated payload".into());
    }
    let (v, rest) = b.split_at(n);
    *b = rest;
    Ok(v)
}
fn count(b: &mut &[u8]) -> Result<usize, String> {
    let n = get(b)?;
    if n > LIMIT || n > b.len() {
        return Err("excessive count".into());
    }
    Ok(n)
}
fn signed(b: &mut Vec<u8>, n: u32) {
    put(b, ((n << 1) ^ ((n as i32 >> 31) as u32)) as usize);
}
fn unsign(b: &mut &[u8]) -> Result<u32, String> {
    let n = get(b)? as u32;
    Ok((n >> 1) ^ (0u32.wrapping_sub(n & 1)))
}
fn xyz(d: TermDelta) -> [u32; 3] {
    [d.g, d.h[0], d.h[1]]
}
fn adjust(d: TermDelta, v: [u32; 3], subtract: bool) -> TermDelta {
    let mut c = xyz(d);
    for i in 0..3 {
        c[i] = if subtract {
            c[i].wrapping_sub(v[i])
        } else {
            c[i].wrapping_add(v[i])
        };
    }
    TermDelta {
        g: c[0],
        h: [c[1], c[2]],
        k_index: d.k_index,
    }
}
fn intern<T: Clone + Eq + std::hash::Hash>(
    map: &mut HashMap<T, u32>,
    values: &mut Vec<T>,
    v: T,
) -> u32 {
    if let Some(&i) = map.get(&v) {
        return i;
    }
    let i = values.len() as u32;
    map.insert(v.clone(), i);
    values.push(v);
    i
}

#[derive(Clone, Debug)]
pub struct PlainLayer {
    pub logw: usize,
    pub nw: usize,
    pub deltas: Vec<TermDelta>,
    pub segments: Vec<Vec<u32>>,
    pub tokens: Vec<u32>,
}
impl PlainLayer {
    // Minimize the widths of the indices actually serialized in the core
    // dictionary, not their expanded execution frequencies.
    pub fn rank_deltas(&mut self) {
        let mut counts = vec![0usize; self.deltas.len()];
        for s in &self.segments {
            for &i in s {
                counts[i as usize] += 1;
            }
        }
        let mut order: Vec<_> = (0..counts.len()).collect();
        order.sort_by_key(|&i| (std::cmp::Reverse(counts[i]), i));
        let mut mapping = vec![0; order.len()];
        let deltas = order
            .iter()
            .enumerate()
            .map(|(new, &old)| {
                mapping[old] = new as u32;
                self.deltas[old]
            })
            .collect();
        for s in &mut self.segments {
            for i in s {
                *i = mapping[*i as usize];
            }
        }
        self.deltas = deltas;
    }
    pub fn stream(&self) -> impl Iterator<Item = TermDelta> + '_ {
        self.tokens.iter().flat_map(|&t| {
            self.segments[t as usize]
                .iter()
                .map(|&i| self.deltas[i as usize])
        })
    }
    fn from_runs(logw: usize, nw: usize, runs: Vec<Vec<TermDelta>>, tokens: Vec<u32>) -> Self {
        let (mut map, mut deltas) = (HashMap::new(), Vec::new());
        let segments = runs
            .into_iter()
            .map(|r| {
                r.into_iter()
                    .map(|d| intern(&mut map, &mut deltas, d))
                    .collect()
            })
            .collect();
        Self {
            logw,
            nw,
            deltas,
            segments,
            tokens,
        }
    }
    fn rechunk(&self, width: usize) -> Self {
        if width == 0 {
            return self.clone();
        }
        let (mut map, mut runs, mut tokens) = (HashMap::new(), Vec::new(), Vec::new());
        let mut run = Vec::with_capacity(width);
        for d in self.stream() {
            run.push(d);
            if run.len() == width {
                tokens.push(intern(&mut map, &mut runs, std::mem::take(&mut run)));
            }
        }
        if !run.is_empty() {
            tokens.push(intern(&mut map, &mut runs, run));
        }
        Self::from_runs(self.logw, self.nw, runs, tokens)
    }
    fn write(&self, b: &mut Vec<u8>) {
        put(b, self.logw);
        put(b, self.nw);
        write_tables(b, &self.deltas, &self.segments);
        put(b, self.tokens.len());
        for &t in &self.tokens {
            put(b, t as usize);
        }
    }
}

#[derive(Clone)]
pub struct PlainFile {
    // Exact original LFC2 geometry and serialized coefficient dictionary.
    pub header: Vec<u8>,
    pub layers: Vec<PlainLayer>,
    pub id: [u8; 32],
}
fn read_tables(b: &mut &[u8]) -> Result<(Vec<TermDelta>, Vec<Vec<u32>>), String> {
    let n = count(b)?;
    let mut deltas = Vec::with_capacity(n);
    for _ in 0..n {
        deltas.push(TermDelta {
            g: unsign(b)?,
            h: [unsign(b)?, unsign(b)?],
            k_index: get(b)? as u32,
        });
    }
    let n = count(b)?;
    let mut segments = Vec::with_capacity(n);
    let mut total = 0usize;
    for _ in 0..n {
        let len = count(b)?;
        total += len;
        if total > LIMIT {
            return Err("segment dictionary limit".into());
        }
        let mut s = Vec::with_capacity(len);
        for _ in 0..len {
            let i = get(b)?;
            if i >= deltas.len() {
                return Err("bad delta index".into());
            }
            s.push(i as u32);
        }
        segments.push(s);
    }
    Ok((deltas, segments))
}
fn write_tables(b: &mut Vec<u8>, deltas: &[TermDelta], segments: &[Vec<u32>]) -> (usize, usize) {
    let start = b.len();
    put(b, deltas.len());
    for &d in deltas {
        for x in xyz(d) {
            signed(b, x);
        }
        put(b, d.k_index as usize);
    }
    let middle = b.len();
    put(b, segments.len());
    for s in segments {
        put(b, s.len());
        for &i in s {
            put(b, i as usize);
        }
    }
    (middle - start, b.len() - middle)
}
impl PlainFile {
    pub fn read_lfc2(bytes: &[u8], field_bytes: usize) -> Result<Self, String> {
        let mut b = bytes;
        if take(&mut b, 4)? != b"LFC2" {
            return Err("not LFC2".into());
        }
        for _ in 0..6 {
            get(&mut b)?;
        }
        let nl = get(&mut b)?;
        if nl > 10_000 {
            return Err("layer limit".into());
        }
        let nc = get(&mut b)?;
        let size = nc
            .checked_mul(field_bytes)
            .ok_or("constant size overflow")?;
        take(&mut b, size)?;
        let header = bytes[..bytes.len() - b.len()].to_vec();
        let mut layers = Vec::new();
        let mut terms = 0usize;
        for _ in 0..nl {
            let logw = get(&mut b)?;
            let nw = get(&mut b)?;
            let (deltas, segments) = read_tables(&mut b)?;
            let n = count(&mut b)?;
            let mut tokens = Vec::with_capacity(n);
            for _ in 0..n {
                let t = get(&mut b)?;
                let seg = segments.get(t).ok_or("bad segment index")?;
                terms += seg.len();
                if terms > LIMIT {
                    return Err("term limit".into());
                }
                tokens.push(t as u32);
            }
            layers.push(PlainLayer {
                logw,
                nw,
                deltas,
                segments,
                tokens,
            });
        }
        let id = take(&mut b, 32)?.try_into().unwrap();
        if !b.is_empty() {
            return Err("trailing data".into());
        }
        Ok(Self { header, layers, id })
    }
    pub fn lfc2(&self) -> Vec<u8> {
        let mut b = self.header.clone();
        for l in &self.layers {
            l.write(&mut b);
        }
        b.extend(self.id);
        b
    }
    pub fn assert_same(&self, other: &Self) {
        assert_eq!(self.header, other.header);
        assert_eq!(self.id, other.id);
        assert_eq!(self.layers.len(), other.layers.len());
        for (a, b) in self.layers.iter().zip(&other.layers) {
            assert_eq!((a.logw, a.nw), (b.logw, b.nw));
            assert!(a.stream().eq(b.stream()), "changed delta stream");
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct Reference {
    core: u32,
    offset: [u32; 3],
}
fn write_ref(b: &mut Vec<u8>, r: Reference) -> usize {
    let has = r.offset != [0; 3];
    put(b, ((r.core as usize) << 1) | has as usize);
    let start = b.len();
    if has {
        for v in r.offset {
            signed(b, v);
        }
    }
    b.len() - start
}
fn read_ref(b: &mut &[u8], ncores: usize) -> Result<Reference, String> {
    let tag = get(b)?;
    let core = (tag >> 1) as u32;
    if core as usize >= ncores {
        return Err("bad relative segment index".into());
    }
    let offset = if tag & 1 == 1 {
        [unsign(b)?, unsign(b)?, unsign(b)?]
    } else {
        [0; 3]
    };
    Ok(Reference { core, offset })
}

#[derive(Default, Debug)]
pub struct Stats {
    pub deltas: usize,
    pub cores: usize,
    pub references: usize,
    pub tokens: usize,
    pub delta_bytes: usize,
    pub segment_bytes: usize,
    pub reference_bytes: usize,
    pub offset_bytes: usize,
    pub token_bytes: usize,
    pub original_segments: usize,
    pub shared_nontrivial_segments: usize,
}

/// all=false is the translation hypothesis. pooled=true stores each distinct
/// (segment, offset) once and uses ordinary integer execution tokens.
pub fn encode(file: &PlainFile, all: bool, pooled: bool, width: usize) -> (Vec<u8>, Stats) {
    let mut b = b"LFR1".to_vec();
    put(&mut b, all as usize);
    put(&mut b, pooled as usize);
    put(&mut b, file.header.len());
    b.extend(&file.header);
    put(&mut b, file.layers.len());
    let mut stats = Stats::default();
    for original in &file.layers {
        let l = original.rechunk(width);
        let (mut map, mut runs) = (HashMap::new(), Vec::new());
        let mut refs = Vec::new();
        let mut bases = Vec::new();
        for s in &l.segments {
            let mut r: Vec<_> = s.iter().map(|&i| l.deltas[i as usize]).collect();
            let offset = r.first().map(|&d| xyz(d)).unwrap_or([0; 3]);
            for (i, d) in r.iter_mut().enumerate() {
                if i == 0 || all {
                    *d = adjust(*d, offset, true);
                }
            }
            let core = intern(&mut map, &mut runs, r);
            if core as usize == bases.len() {
                bases.push(offset);
            }
            let base = bases[core as usize];
            refs.push(Reference {
                core,
                offset: std::array::from_fn(|i| offset[i].wrapping_sub(base[i])),
            });
        }
        // Use an actual instance as the representative, not an artificial
        // zero-start run. An unshared segment then needs no offset payload.
        for (run, base) in runs.iter_mut().zip(bases) {
            for (i, d) in run.iter_mut().enumerate() {
                if i == 0 || all {
                    *d = adjust(*d, base, false);
                }
            }
        }
        stats.original_segments += l.segments.len();
        let mut uses = vec![0; runs.len()];
        for r in &refs {
            uses[r.core as usize] += 1;
        }
        stats.shared_nontrivial_segments += uses
            .iter()
            .zip(&runs)
            .filter(|(n, r)| **n > 1 && r.len() > 1)
            .map(|(n, _)| n - 1)
            .sum::<usize>();
        let mut normalized = PlainLayer::from_runs(l.logw, l.nw, runs, Vec::new());
        normalized.rank_deltas();
        // Rank the IDs by how often this layout actually writes them. This is
        // offline dictionary packing, not circuit term sorting.
        let mut counts = vec![0usize; normalized.segments.len()];
        if pooled {
            for r in &refs {
                counts[r.core as usize] += 1;
            }
        } else {
            for &t in &l.tokens {
                counts[refs[t as usize].core as usize] += 1;
            }
        }
        let mut order: Vec<_> = (0..counts.len()).collect();
        order.sort_by_key(|&i| (std::cmp::Reverse(counts[i]), i));
        let mut mapping = vec![0u32; order.len()];
        normalized.segments = order
            .iter()
            .enumerate()
            .map(|(new, &old)| {
                mapping[old] = new as u32;
                std::mem::take(&mut normalized.segments[old])
            })
            .collect();
        for r in &mut refs {
            r.core = mapping[r.core as usize];
        }
        put(&mut b, l.logw);
        put(&mut b, l.nw);
        let (db, sb) = write_tables(&mut b, &normalized.deltas, &normalized.segments);
        stats.deltas += normalized.deltas.len();
        stats.cores += normalized.segments.len();
        stats.delta_bytes += db;
        stats.segment_bytes += sb;
        stats.tokens += l.tokens.len();
        if pooled {
            let (mut map, mut table) = (HashMap::new(), Vec::new());
            let mut tokens: Vec<_> = l
                .tokens
                .iter()
                .map(|&t| intern(&mut map, &mut table, refs[t as usize]))
                .collect();
            let mut counts = vec![0usize; table.len()];
            for &t in &tokens {
                counts[t as usize] += 1;
            }
            let mut order: Vec<_> = (0..counts.len()).collect();
            order.sort_by_key(|&i| (std::cmp::Reverse(counts[i]), i));
            let mut mapping = vec![0u32; table.len()];
            table = order
                .iter()
                .enumerate()
                .map(|(new, &old)| {
                    mapping[old] = new as u32;
                    table[old]
                })
                .collect();
            for t in &mut tokens {
                *t = mapping[*t as usize];
            }
            let start = b.len();
            put(&mut b, table.len());
            for &r in &table {
                stats.offset_bytes += write_ref(&mut b, r);
            }
            stats.reference_bytes += b.len() - start;
            stats.references += table.len();
            let start = b.len();
            put(&mut b, tokens.len());
            for t in tokens {
                put(&mut b, t as usize);
            }
            stats.token_bytes += b.len() - start;
        } else {
            let start = b.len();
            put(&mut b, l.tokens.len());
            for &t in &l.tokens {
                stats.offset_bytes += write_ref(&mut b, refs[t as usize]);
            }
            stats.reference_bytes += b.len() - start;
            stats.references += l.tokens.len();
        }
    }
    b.extend(file.id);
    (b, stats)
}

pub fn decode(bytes: &[u8]) -> Result<PlainFile, String> {
    let mut b = bytes;
    if take(&mut b, 4)? != b"LFR1" {
        return Err("not LFR1".into());
    }
    let all = get(&mut b)?;
    let pooled = get(&mut b)?;
    if all > 1 || pooled > 1 {
        return Err("unknown LFR1 mode".into());
    }
    let len = count(&mut b)?;
    let header = take(&mut b, len)?.to_vec();
    if !header.starts_with(b"LFC2") {
        return Err("bad embedded header".into());
    }
    let nl = count(&mut b)?;
    if nl > 10_000 {
        return Err("layer limit".into());
    }
    let mut layers = Vec::new();
    let mut terms = 0usize;
    let mut dictionary_terms = 0usize;
    for _ in 0..nl {
        let logw = get(&mut b)?;
        let nw = get(&mut b)?;
        let (deltas, segments) = read_tables(&mut b)?;
        let n = count(&mut b)?;
        let mut refs = Vec::with_capacity(n);
        for _ in 0..n {
            refs.push(read_ref(&mut b, segments.len())?);
        }
        let (refs, tokens) = if pooled == 1 {
            let n = count(&mut b)?;
            let mut tokens = Vec::with_capacity(n);
            for _ in 0..n {
                let t = get(&mut b)?;
                if t >= refs.len() {
                    return Err("bad reference token".into());
                }
                tokens.push(t as u32);
            }
            (refs, tokens)
        } else {
            let (mut map, mut table) = (HashMap::new(), Vec::new());
            let tokens = refs
                .into_iter()
                .map(|r| intern(&mut map, &mut table, r))
                .collect();
            (table, tokens)
        };
        let mut runs = Vec::with_capacity(refs.len());
        for r in refs {
            let s = &segments[r.core as usize];
            dictionary_terms += s.len();
            if dictionary_terms > LIMIT {
                return Err("expanded dictionary limit".into());
            }
            runs.push(
                s.iter()
                    .enumerate()
                    .map(|(i, &idx)| {
                        let d = deltas[idx as usize];
                        if i == 0 || all == 1 {
                            adjust(d, r.offset, false)
                        } else {
                            d
                        }
                    })
                    .collect::<Vec<_>>(),
            );
        }
        for &t in &tokens {
            terms += runs[t as usize].len();
            if terms > LIMIT {
                return Err("expanded term limit".into());
            }
        }
        layers.push(PlainLayer::from_runs(logw, nw, runs, tokens));
    }
    let id = take(&mut b, 32)?.try_into().unwrap();
    if !b.is_empty() {
        return Err("trailing LFR1 data".into());
    }
    Ok(PlainFile { header, layers, id })
}

pub fn boundary_counts(file: &PlainFile) -> (usize, usize, usize) {
    let (mut only, mut inside, mut all) = (0, 0, 0);
    for l in &file.layers {
        let (mut boundary, mut interior) = (HashSet::new(), HashSet::new());
        for &t in &l.tokens {
            for (i, &d) in l.segments[t as usize].iter().enumerate() {
                if i == 0 {
                    boundary.insert(l.deltas[d as usize]);
                } else {
                    interior.insert(l.deltas[d as usize]);
                }
            }
        }
        only += boundary.difference(&interior).count();
        inside += interior.len();
        all += boundary.union(&interior).count();
    }
    (all, only, inside)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn d(g: u32, h0: u32, h1: u32, k: u32) -> TermDelta {
        TermDelta {
            g,
            h: [h0, h1],
            k_index: k,
        }
    }
    fn fixture(runs: Vec<Vec<TermDelta>>) -> PlainFile {
        let tokens = (0..runs.len() as u32).chain(0..runs.len() as u32).collect();
        PlainFile {
            header: b"LFC2fixture".to_vec(),
            id: [17; 32],
            layers: vec![PlainLayer::from_runs(5, 32, runs, tokens)],
        }
    }
    #[test]
    fn translation_changes_only_entry_delta() {
        let f = fixture(vec![
            vec![d(1, 2, 3, 0), d(2, 3, 4, 1)],
            vec![d(9, 8, 7, 0), d(2, 3, 4, 1)],
        ]);
        let (b, s) = encode(&f, false, true, 0);
        assert_eq!(s.cores, 1);
        f.assert_same(&decode(&b).unwrap());
        assert_eq!(encode(&f, true, true, 0).1.cores, 2);
    }
    #[test]
    fn shared_ports_and_coefficients_prevent_false_matches() {
        let f = fixture(vec![
            vec![d(1, 2, 3, 0), d(2, 3, 4, 1)],
            vec![d(9, 8, 7, 0), d(2, 3, 5, 1)],
            vec![d(9, 8, 7, 1), d(2, 3, 4, 1)],
        ]);
        assert_eq!(encode(&f, false, true, 0).1.cores, 3);
    }
    #[test]
    fn modes_rechunking_negatives_duplicates_and_empty_roundtrip() {
        let f = fixture(vec![
            vec![],
            vec![d(u32::MAX, 2, 3, 0)],
            vec![d(9, 8, 7, 0), d(2, 3, 4, 1), d(2, 3, 4, 1)],
        ]);
        for all in [false, true] {
            for pool in [false, true] {
                for width in [0, 1, 2, 8, 32] {
                    let (b, _) = encode(&f, all, pool, width);
                    f.assert_same(&decode(&b).unwrap());
                }
            }
        }
    }
    #[test]
    fn truncated_and_invalid_payloads_rejected() {
        let f = fixture(vec![vec![d(1, 2, 3, 0)]]);
        let (b, _) = encode(&f, false, true, 0);
        for n in 0..b.len() {
            assert!(decode(&b[..n]).is_err());
        }
        let mut bad = b.clone();
        bad[4] = 2;
        assert!(decode(&bad).is_err());
        let mut bad = b.clone();
        bad.push(0);
        assert!(decode(&bad).is_err());
        assert!(read_ref(&mut &[127u8][..], 1).is_err());
        assert!(read_tables(&mut &[0, 1, 1, 0][..]).is_err());
    }
}
