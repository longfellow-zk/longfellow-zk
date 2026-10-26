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

//! Interleaved raw samples for all explicit v9 compiler/kernel choices.
use std::time::Instant;

use longfellow_zk::{
    compile::algebra::CompileNat,
    mdoc::{
        circuits::parse_test_data,
        development_provider as provider,
        v2::{
            packed_v9::{self, prover::run_mdoc_prover_inner_with_window},
            req_attr,
        },
    },
    runtime::random::DeterministicRng,
};
#[path = "../../../../benches/support/memory.rs"]
mod memory;
fn main() {
    let quick = std::env::var_os("MDOC_V9_QUICK").is_some();
    let attributes = std::env::var("MDOC_V9_ATTRIBUTES")
        .unwrap_or("2".into())
        .parse::<usize>()
        .unwrap();
    assert!(attributes == 2 || attributes == 4);
    let samples = std::env::var("MDOC_V9_SAMPLES")
        .unwrap_or("3".into())
        .parse::<usize>()
        .unwrap();
    assert!(samples > 0);
    let cache = std::env::var_os("MDOC_V9_CACHE").map(std::path::PathBuf::from);
    if let Some(dir) = &cache {
        std::fs::create_dir_all(dir).unwrap()
    }
    let data = &longfellow_zk::mdoc::testcases::vectors::TEST_DATA;
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(data);
    let attrs = parsed
        .attrs
        .iter()
        .cycle()
        .take(attributes)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect::<Vec<_>>();
    let bundles = (0..if quick { 1 } else { 3 })
        .map(|variant| {
            let path = cache
                .as_ref()
                .map(|d| d.join(format!("v9-flat-{attributes}-{variant}.cache")));
            let bundle = if let Some(p) = path.as_ref().filter(|p| p.exists()) {
                provider::read_packed_v9(p).unwrap()
            } else {
                provider::compile_packed_v9_variant(attributes, variant).unwrap()
            };
            assert_eq!(bundle.spec().num_attributes, attributes);
            assert_eq!(bundle.spec().manifest.compiler_variant, variant);
            if let Some(p) = path {
                provider::write_packed_v9(&p, &bundle).unwrap()
            }
            bundle
        })
        .collect::<Vec<_>>();
    eprintln!(
        "Experimental flat-trace v9; memory instrumentation={}; no kernel selected automatically",
        cfg!(feature = "bench-memory")
    );
    println!("attributes,variant,window,sample,prover_ms,verifier_ms,proof_bytes,prover_heap,verifier_heap");
    let mut results = vec![Vec::new(); 15];
    let mut references: Vec<Option<Vec<u8>>> = vec![None; 3];
    for sample in 0..samples {
        // Rotate the order between repetitions to reduce systematic warmup bias.
        for offset in 0..if quick { 1 } else { 15 } {
            let choice = if quick { 0 } else { (offset + sample * 7) % 15 };
            let variant = choice / 5;
            let window = choice % 5;
            let bundle = &bundles[variant];
            let spec = bundle.spec();
            memory::reset_peak();
            let prover_baseline = memory::get_current_allocated();
            let prover_begin = Instant::now();
            let proof = run_mdoc_prover_inner_with_window(
                spec,
                bundle.compressed(),
                data.mdoc,
                data.pkx,
                data.pky,
                data.transcript,
                &attrs,
                now,
                data.doc_type,
                &mut DeterministicRng::new(42),
                if window == 0 { None } else { Some(window) },
            )
            .unwrap();
            let prover_ms = prover_begin.elapsed().as_secs_f64() * 1000.;
            let prover_heap = memory::get_peak_allocated().saturating_sub(prover_baseline);
            if let Some(reference) = &references[variant] {
                assert_eq!(&proof, reference, "kernel proof mismatch")
            } else {
                references[variant] = Some(proof.clone())
            }
            memory::reset_peak();
            let verifier_baseline = memory::get_current_allocated();
            let verifier_begin = Instant::now();
            packed_v9::run_mdoc_verifier_inner(
                spec,
                bundle.compressed(),
                data.pkx,
                data.pky,
                data.transcript,
                &attrs,
                now,
                data.doc_type,
                &proof,
            )
            .unwrap();
            let verifier_ms = verifier_begin.elapsed().as_secs_f64() * 1000.;
            let verifier_heap = memory::get_peak_allocated().saturating_sub(verifier_baseline);
            println!("{attributes},{variant},{window},{sample},{prover_ms:.6},{verifier_ms:.6},{},{prover_heap},{verifier_heap}",proof.len());
            results[choice].push((prover_ms, verifier_ms));
        }
    }
    for (choice, values) in results.iter_mut().enumerate() {
        if values.is_empty() {
            continue;
        }
        values.sort_by(|a, b| a.0.total_cmp(&b.0));
        let p = values[values.len() / 2].0;
        values.sort_by(|a, b| a.1.total_cmp(&b.1));
        let v = values[values.len() / 2].1;
        eprintln!("median attributes={attributes} variant={} window={}: prover={p:.3} ms verifier={v:.3} ms",choice/5,choice%5);
    }
}
