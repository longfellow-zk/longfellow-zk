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

//! Compare streaming and sorted canonical IDs on the same immutable saved LFC2.
//! Timing: default allocator, alternating methods after warmup.
//! Memory: bench-memory, one method/one invocation in a fresh process.

#[path = "support/memory.rs"]
mod memory;

use core_proto::{
    circuit::{compute_canonical_id, compute_id},
    reader::CircuitReader,
    FieldID, SerializableField,
};
use std::{hint::black_box, time::Instant};

fn resident_kib() -> (usize, usize) {
    let status = std::fs::read_to_string("/proc/self/status").expect("Linux procfs required");
    let value = |key: &str| {
        status
            .lines()
            .find_map(|line| {
                line.strip_prefix(key)
                    .map(|v| v.split_whitespace().next().unwrap().parse().unwrap())
            })
            .unwrap()
    };
    (value("VmRSS:"), value("VmHWM:"))
}

fn benchmark<F: SerializableField>(dataset: &str, f: &F, field_id: FieldID) {
    let dir =
        std::env::var("CID_CIRCUIT_DIR").unwrap_or_else(|_| "target/traversal-circuits".into());
    let bytes = std::fs::read(format!("{dir}/{dataset}--kind_abs_lex0213_r5.lfc2")).unwrap();
    // Do not hash while loading: memory runs measure only the selected ID method.
    let (circuit, tail) = CircuitReader::new(f, field_id)
        .from_bytes(&bytes, false)
        .unwrap();
    assert!(tail.is_empty());
    drop(bytes);
    let method = std::env::var("CID_METHOD").unwrap_or_else(|_| "both".into());
    assert!(["both", "current", "canonical"].contains(&method.as_str()));
    let repeats: usize = std::env::var("CID_REPEATS")
        .unwrap_or_else(|_| if method == "both" { "9" } else { "1" }.into())
        .parse()
        .unwrap();
    assert!(repeats > 0);
    if cfg!(feature = "bench-memory") {
        assert!(
            method != "both" && repeats == 1,
            "memory runs require one method, one invocation, and a fresh process"
        );
    }
    let mut times = [Vec::with_capacity(repeats), Vec::with_capacity(repeats)];
    let mut heaps = [0usize; 2];
    let mut baselines = [0usize; 2];
    let mut ids = [None, None];
    let (rss_before, hwm_before) = resident_kib();
    if method == "both" {
        black_box(compute_id(f, &circuit.raw));
        black_box(compute_canonical_id(f, &circuit.raw));
    }
    for repeat in 0..repeats {
        for offset in 0..2 {
            let index = (repeat + offset) % 2;
            if (method == "current" && index != 0) || (method == "canonical" && index != 1) {
                continue;
            }
            let measurement = memory::Measurement::start();
            let start = Instant::now();
            let id = black_box(if index == 0 {
                compute_id(black_box(f), black_box(&circuit.raw))
            } else {
                compute_canonical_id(black_box(f), black_box(&circuit.raw))
            });
            let elapsed = start.elapsed().as_secs_f64() * 1000.;
            let heap = measurement.finish();
            times[index].push(elapsed);
            heaps[index] = heaps[index].max(heap.additional());
            baselines[index] = heap.baseline;
            if let Some(previous) = ids[index] {
                assert_eq!(previous, id);
            }
            ids[index] = Some(id);
        }
    }
    let (rss_after, hwm_after) = resident_kib();
    let nterms: usize = circuit.raw.layers.iter().map(|l| l.num_terms()).sum();
    let largest_layer = circuit
        .raw
        .layers
        .iter()
        .map(|l| l.num_terms())
        .max()
        .unwrap_or(0);
    println!("CID_CIRCUIT dataset={dataset} terms={nterms} largest_layer={largest_layer} constants={} layers={}",
        circuit.raw.constants.len(), circuit.raw.layers.len());
    for (index, name) in ["current", "canonical"].iter().enumerate() {
        if let Some(id) = ids[index] {
            let hex: String = id.iter().map(|b| format!("{b:02x}")).collect();
            println!("CID_RESULT dataset={dataset} method={name} tracked={} ms={:?} baseline_heap={} peak_additional_heap={} rss_before_kib={rss_before} hwm_before_kib={hwm_before} rss_after_kib={rss_after} hwm_after_kib={hwm_after} id={hex}",
                cfg!(feature = "bench-memory"), times[index], baselines[index], heaps[index]);
        }
    }
    // Check the saved legacy ID and non-mutation outside timing/memory samples.
    assert_eq!(compute_id(f, &circuit.raw), circuit.id);
    if let Some(current) = ids[0] {
        assert_eq!(current, circuit.id);
    }
}

#[test]
#[ignore = "saved-circuit ID timing and peak-memory benchmark"]
fn circuit_id_benchmark() {
    let dataset = std::env::var("CID_DATASET").expect("set CID_DATASET");
    match dataset.as_str() {
        "mdoc_hash1" | "mdoc_hash2" | "mdoc_hash3" | "mdoc_hash4" => benchmark(
            &dataset,
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            FieldID::Gf2_128,
        ),
        "mdoc_sig" => benchmark(
            &dataset,
            &runtime_algebra::p256::P256Field::new(),
            FieldID::P256,
        ),
        "mldsa44" | "mldsa65" => benchmark(
            &dataset,
            &circuits_experimental::mldsa::algebra::RuntimeFp24Ext6::new(),
            FieldID::None,
        ),
        _ => panic!("unknown CID_DATASET: {dataset}"),
    }
}
