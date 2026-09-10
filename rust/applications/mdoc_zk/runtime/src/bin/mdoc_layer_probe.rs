// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Per-layer delta / segment / token counts for the shipped mdoc circuits.
//!
//! These are the numbers that decide Lean ingestion cost, and they are *not* predictable from
//! term count.  The one-block SHA-256 circuit turned out to compress not at all, which made its
//! parse modules ~10x denser than ECDSA2's at comparable size; that difference, not size, is
//! what made them unbuildable.  So measure mdoc directly before planning against it.
//!
//! For each layer we report:
//!   * `terms`     — expanded term count, drives the *expansion* stage
//!   * `deltas`    — distinct delta tuples; every expanded term does one `deltas[i]?` lookup,
//!                   and that lookup is a list walk in the Lean kernel, so this is the
//!                   quadratic factor
//!   * `segs`      — dictionary entries; one `segments[i]?` per term, same problem
//!   * `symbols`   — total symbols across segments, i.e. the parse-stage literal size
//!   * `tokens`    — token stream length
//!
//! Run with `--release`; decompression of the shipped archives is not cheap.

use compile_compiler::segment_circuit;
use core_proto::{writer::CircuitWriter, FieldID, Layer, SerializableField};
use mdoc_zk_runtime::proto::decompress_circuits;

/// Kernel cost per list step, measured on Lean 4.31 (`0.515 us`).
const US_PER_STEP: f64 = 0.515e-6;

fn report<F: SerializableField>(label: &str, circuit: &core_proto::circuit::Circuit<F>) {
    let layers = &circuit.raw.layers;
    println!(
        "\n=== {label}: {} layers, {} terms, {} constants ===",
        layers.len(),
        layers.iter().map(Layer::num_terms).sum::<usize>(),
        circuit.raw.constants.len()
    );
    println!(
        "{:>3}  {:>9}  {:>8}  {:>8}  {:>9}  {:>8}  {:>7}  {:>12}",
        "L", "terms", "deltas", "segs", "symbols", "tokens", "sym/trm", "expand(CPU)"
    );
    let mut total_expand = 0.0f64;
    let mut worst_symbols = 0usize;
    for (index, layer) in layers.iter().enumerate() {
        let terms = layer.num_terms();
        let deltas = layer.deltas().len();
        let segs = layer.num_segments();
        let symbols: usize = layer.delta_segments().iter().map(Vec::len).sum();
        let tokens = layer.delta_tokens().len();
        // Per expanded term the decoder indexes tokens, segments and deltas; each index is a
        // list walk of about half the container.
        let per_term = tokens as f64 / 2.0 + segs as f64 / 2.0 + deltas as f64 / 2.0 + 16.0;
        let expand = per_term * terms as f64 * US_PER_STEP;
        total_expand += expand;
        worst_symbols = worst_symbols.max(symbols);
        println!(
            "{index:>3}  {terms:>9}  {deltas:>8}  {segs:>8}  {symbols:>9}  {tokens:>8}  \
             {:>7.2}  {:>10.1} s",
            symbols as f64 / terms.max(1) as f64,
            expand
        );
    }
    println!(
        "  expansion total {:.1} CPU-hours   worst per-layer parse literal {worst_symbols} symbols",
        total_expand / 3600.0
    );
    println!(
        "  with an O(log n) lookup instead of the list walk: {:.1} CPU-minutes",
        total_expand / 60.0 * (17.0 / (layers.iter().map(|l| l.deltas().len()).max().unwrap_or(2) as f64 / 2.0))
    );
}

fn main() {
    let p256 = runtime_algebra::p256::P256Field::new();
    let gf2 = runtime_algebra::gf2_128::Gf2_128Field::new();
    let dir = format!("{}/../artifacts/circuits", env!("CARGO_MANIFEST_DIR"));

    // One representative version-7 circuit unless a hash is given.
    let hash = std::env::args()
        .nth(1)
        .unwrap_or_else(|| mdoc_zk_artifacts::all_circuit_hashes()[0].to_string());
    let bytes = std::fs::read(format!("{dir}/{hash}"))
        .or_else(|_| std::fs::read(format!("{dir}/{hash}.lfa1")))
        .unwrap_or_else(|e| panic!("read circuit {hash}: {e}"));
    let (c_sig, c_hash) = decompress_circuits(&bytes, &p256, &gf2).expect("decompress");

    // Ship-shape means segmented; the unsegmented form is not what gets committed.
    let seg_sig = segment_circuit(&p256, &c_sig);
    let seg_hash = segment_circuit(&gf2, &c_hash);
    println!("circuit {hash}");
    report("signature (P256)", &seg_sig);
    report("hash (GF(2^128))", &seg_hash);
    locality("signature", &seg_sig);
    locality("hash", &seg_hash);

    let wsig = CircuitWriter::new(&p256, FieldID::P256);
    let whash = CircuitWriter::new(&gf2, FieldID::Gf2_128);
    let sig3 = wsig.to_bytes_lfc2(&seg_sig);
    let hash3 = whash.to_bytes_lfc2(&seg_hash);
    println!(
        "\nLFC2 bytes: signature {} ({} pages), hash {} ({} pages)",
        sig3.len(),
        sig3.len().div_ceil(4096),
        hash3.len(),
        hash3.len().div_ceil(4096)
    );
}

/// How local are the dictionary references?
///
/// Three of the decoder's four lookups walk a container whose position only ever *increases*
/// (`tokens[outer]`, `segment[deltaOffset]`), so they are sequential and need no index at all —
/// carrying the residual list makes them O(1).  The genuinely random ones are the dictionary
/// hits: `segments[token]` and `deltas[symbol]`.  If consecutive references are *near* each
/// other, a cursor holding a zipper over the dictionary reaches the next entry in O(|jump|),
/// and a scheduler can order the dictionary to make jumps small by construction.  This measures
/// the jumps a scheduler would have to beat.
fn locality<F: SerializableField>(label: &str, circuit: &core_proto::circuit::Circuit<F>) {
    println!("\n=== {label}: dictionary reference locality ===");
    println!(
        "{:>3} {:>9} {:>10} {:>10} {:>10}   {:>9} {:>10} {:>10}",
        "L", "tokens", "tok|jump|", "tok med", "tok p90", "symbols", "sym|jump|", "sym med"
    );
    for (index, layer) in circuit.raw.layers.iter().enumerate() {
        let toks = layer.delta_tokens();
        if toks.len() < 64 {
            continue;
        }
        let mut tj: Vec<u64> = toks
            .windows(2)
            .map(|w| (w[1] as i64 - w[0] as i64).unsigned_abs())
            .collect();
        let tmean = tj.iter().sum::<u64>() as f64 / tj.len().max(1) as f64;
        tj.sort_unstable();
        let tmed = tj[tj.len() / 2];
        let tp90 = tj[tj.len() * 9 / 10];

        // Symbol jumps, in the order expansion actually visits them.
        let mut sj: Vec<u64> = Vec::new();
        let mut prev: Option<u32> = None;
        let mut symbols = 0usize;
        for &tok in toks {
            for &d in &layer.delta_segments()[tok as usize] {
                symbols += 1;
                if let Some(p) = prev {
                    sj.push((d as i64 - p as i64).unsigned_abs());
                }
                prev = Some(d);
            }
        }
        let smean = sj.iter().sum::<u64>() as f64 / sj.len().max(1) as f64;
        sj.sort_unstable();
        let smed = if sj.is_empty() { 0 } else { sj[sj.len() / 2] };
        println!(
            "{index:>3} {:>9} {tmean:>10.1} {tmed:>10} {tp90:>10}   {symbols:>9} {smean:>10.1} {smed:>10}",
            toks.len()
        );
    }
}
