// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! How much repetition is in a layer's delta-index stream, and how much does `segment_layer`
//! actually capture?
//!
//! `segment_layer` looks for repeated windows of exactly `W = 32` **at offsets that are
//! multiples of `W`** (pass 1 strides `i += W`).  This probe reports, per layer, what a
//! stride-1 scan would find instead, and the strongest self-similarity period, so the cost of
//! that alignment restriction can be read off directly.

use std::collections::{HashMap, HashSet};

use compile_algebra::p256::P256Field;
use core_proto::{reader::CircuitReader, FieldID};

fn main() -> Result<(), String> {
    let path = std::env::args().nth(1).ok_or("usage: segment_probe FILE.lfc2")?;
    let bytes = std::fs::read(&path).map_err(|e| format!("read {path}: {e}"))?;
    let field = P256Field::new();
    let (circuit, _) = CircuitReader::new(&field, FieldID::P256).from_bytes_lfc2(&bytes, true)?;

    for (index, layer) in circuit.raw.layers.iter().enumerate() {
        let mut stream = Vec::with_capacity(layer.num_terms());
        layer.for_each_delta_index(|d| stream.push(d));
        if stream.len() < 256 {
            continue;
        }
        println!(
            "layer {index}: {} terms, {} distinct deltas, {} segments now",
            stream.len(),
            stream.iter().collect::<HashSet<_>>().len(),
            layer.num_segments()
        );

        for w in [8usize, 16, 32, 64, 128] {
            if stream.len() < w {
                continue;
            }
            let aligned: HashSet<&[u32]> = stream.chunks_exact(w).collect();
            let sliding: HashSet<&[u32]> = stream.windows(w).collect();
            let aligned_total = stream.len() / w;
            let sliding_total = stream.len() - w + 1;
            println!(
                "  W={w:<4} aligned {aligned:>7}/{aligned_total:<7} distinct ({ar:.2}x)   \
                 sliding {sliding:>7}/{sliding_total:<7} distinct ({sr:.2}x)",
                aligned = aligned.len(),
                sliding = sliding.len(),
                ar = aligned_total as f64 / aligned.len() as f64,
                sr = sliding_total as f64 / sliding.len() as f64,
            );
        }

        // Strongest period: the shift that most often maps a position onto an equal value.
        let mut best: Vec<(usize, f64)> = (1..stream.len().min(4096))
            .map(|p| {
                let matches = stream[p..]
                    .iter()
                    .zip(&stream)
                    .filter(|(a, b)| a == b)
                    .count();
                (p, matches as f64 / (stream.len() - p) as f64)
            })
            .collect();
        best.sort_by(|a, b| b.1.total_cmp(&a.1));
        let top: Vec<String> = best
            .iter()
            .take(4)
            .map(|(p, r)| format!("p={p} ({:.0}%)", r * 100.0))
            .collect();
        println!("  strongest periods: {}", top.join(", "));

        // Run-length view: how long are the maximal runs that recur verbatim elsewhere?
        let mut first_seen: HashMap<&[u32], usize> = HashMap::new();
        let mut covered = 0usize;
        let mut i = 0usize;
        while i < stream.len() {
            let mut best_len = 0usize;
            let mut len = 4usize;
            while i + len <= stream.len() && len <= 512 {
                if first_seen.contains_key(&stream[i..i + len]) {
                    best_len = len;
                    len += 4;
                } else {
                    break;
                }
            }
            for len in 4..=64.min(stream.len() - i) {
                first_seen.entry(&stream[i..i + len]).or_insert(i);
            }
            if best_len > 0 {
                covered += best_len;
                i += best_len;
            } else {
                i += 1;
            }
        }
        println!(
            "  greedy back-reference coverage: {covered}/{} ({:.0}%)",
            stream.len(),
            covered as f64 / stream.len() as f64 * 100.0
        );

        // Does the *ordering* hide the repetition?  The canonical order is morton on
        // (h0,h1) then g, chosen for the sumcheck protocol rather than for compressibility.
        // Re-sort the same terms under other keys and re-measure what a 32-gram scan sees.
        let mut terms: Vec<(u32, u32, u32)> = Vec::with_capacity(layer.num_terms());
        layer.for_each_term(&circuit.raw.constants, |t| terms.push((t.g, t.h0, t.h1)));
        for (label, key) in [
            ("as-serialized     ", None),
            ("sort by (g,h0,h1) ", Some(0u8)),
            ("sort by (h0,g,h1) ", Some(1u8)),
            ("sort by (h1,h0,g) ", Some(2u8)),
        ] {
            let mut ordered = terms.clone();
            match key {
                None => {}
                Some(0) => ordered.sort_unstable(),
                Some(1) => ordered.sort_unstable_by_key(|&(g, h0, h1)| (h0, g, h1)),
                _ => ordered.sort_unstable_by_key(|&(g, h0, h1)| (h1, h0, g)),
            }
            // Delta stream in that order, exactly as LFC3 forms it.
            let mut deltas: Vec<(u32, u32, u32)> = Vec::with_capacity(ordered.len());
            let (mut pg, mut p0, mut p1) = (0u32, 0u32, 0u32);
            for &(g, h0, h1) in &ordered {
                deltas.push((
                    g.wrapping_sub(pg),
                    h0.wrapping_sub(p0),
                    h1.wrapping_sub(p1),
                ));
                (pg, p0, p1) = (g, h0, h1);
            }
            let distinct: HashSet<&(u32, u32, u32)> = deltas.iter().collect();
            let grams: HashSet<&[(u32, u32, u32)]> = deltas.windows(32).collect();
            println!(
                "  {label} {:>6} distinct deltas, {:>6} distinct 32-grams ({:.2}x)",
                distinct.len(),
                grams.len(),
                (deltas.len() - 31) as f64 / grams.len() as f64,
            );
        }
        // Delta-index jumps in expansion order: what a zipper over the delta table would pay
        // per term, against `deltas/2` for indexing from the head.
        let mut jumps: Vec<u64> = Vec::new();
        let mut prev: u32 = 0;
        for &tok in layer.delta_tokens() {
            for &d in &layer.delta_segments()[tok as usize] {
                jumps.push((d as i64 - prev as i64).unsigned_abs());
                prev = d;
            }
        }
        let mean = jumps.iter().sum::<u64>() as f64 / jumps.len().max(1) as f64;
        jumps.sort_unstable();
        println!(
            "  delta zipper: mean |jump| {:.1}, median {}  vs indexing {:.0}  => {:.2}x",
            mean,
            jumps[jumps.len() / 2],
            layer.deltas().len() as f64 / 2.0,
            layer.deltas().len() as f64 / 2.0 / mean.max(0.01)
        );
        println!();
    }
    Ok(())
}
