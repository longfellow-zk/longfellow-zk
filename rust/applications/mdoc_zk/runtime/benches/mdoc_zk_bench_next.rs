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

//! NEXT v9 default: end-to-end timing and optional allocation measurements.
use std::time::Instant;

use longfellow_zk::{
    compile::algebra::CompileNat,
    mdoc::{
        circuits::parse_test_data,
        development_provider as provider,
        v2::{self, req_attr},
    },
    runtime::random::DeterministicRng,
};
#[path = "../../../../benches/support/coefficients.rs"]
mod coefficients;
#[path = "../../../../benches/support/memory.rs"]
mod memory;
fn main() {
    let n = std::env::var("MDOC_V9_ATTRIBUTES")
        .unwrap_or("2".into())
        .parse::<usize>()
        .unwrap();
    assert!((1..=4).contains(&n));
    let samples = std::env::var("MDOC_V9_SAMPLES")
        .unwrap_or("3".into())
        .parse::<usize>()
        .unwrap();
    assert!(samples > 0);
    let path = std::env::var_os("MDOC_V9_CACHE").map(|dir| {
        std::fs::create_dir_all(&dir).unwrap();
        std::path::PathBuf::from(dir).join(format!("next-v9-{n}.cache"))
    });
    let classes = coefficients::from_env(|one, minus_one| {
        longfellow_zk::core::proto::fixed::CoefficientClasses { one, minus_one }
    });
    let bundle = if let Some(p) = path.as_ref().filter(|p| p.exists()) {
        provider::read_next_file(p).unwrap()
    } else {
        provider::compile_next_with_classes(n, classes).unwrap()
    };
    if let Some(p) = path {
        provider::write_next_file(&p, &bundle).unwrap()
    }
    let p = longfellow_zk::runtime::algebra::p256::P256Field::new();
    let f = longfellow_zk::runtime::algebra::gf2_128::Gf2_128Field::new();
    let (sig, hash) = v2::provider::load(bundle.spec(), bundle.compressed(), &p, &f).unwrap();
    eprintln!(
        "circuit attributes={n}: zstd={} raw={} decoded_heap={}",
        bundle.compressed().len(),
        zstd::decode_all(bundle.compressed()).unwrap().len(),
        sig.heap_bytes() + hash.heap_bytes()
    );
    eprintln!("term counts [quadratic,linear,constant] x [zero,one,minus_one,general]: hash={:?} signature={:?}",hash.term_class_breakdown(&f),sig.term_class_breakdown(&p));
    drop((sig, hash));
    let data = &longfellow_zk::mdoc::testcases::vectors::TEST_DATA;
    let (_, parsed, now) = parse_test_data::<4, CompileNat<4>>(data);
    let attrs = parsed
        .attrs
        .iter()
        .cycle()
        .take(n)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect::<Vec<_>>();
    println!("attributes,sample,prover_ms,verifier_ms,proof_bytes,prover_heap,verifier_heap");
    let mut ps = Vec::new();
    let mut vs = Vec::new();
    for sample in 0..samples {
        memory::reset_peak();
        let baseline = memory::get_current_allocated();
        let start = Instant::now();
        let proof = v2::run_mdoc_prover_inner(
            bundle.spec(),
            bundle.compressed(),
            data.mdoc,
            data.pkx,
            data.pky,
            data.transcript,
            &attrs,
            now,
            data.doc_type,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
        let pm = start.elapsed().as_secs_f64() * 1000.;
        let ph = memory::get_peak_allocated().saturating_sub(baseline);
        memory::reset_peak();
        let baseline = memory::get_current_allocated();
        let start = Instant::now();
        v2::run_mdoc_verifier_inner(
            bundle.spec(),
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
        let vm = start.elapsed().as_secs_f64() * 1000.;
        let vh = memory::get_peak_allocated().saturating_sub(baseline);
        println!("{n},{sample},{pm:.6},{vm:.6},{},{ph},{vh}", proof.len());
        ps.push(pm);
        vs.push(vm);
    }
    ps.sort_by(f64::total_cmp);
    vs.sort_by(f64::total_cmp);
    eprintln!(
        "median: prover={:.3} ms verifier={:.3} ms",
        ps[samples / 2],
        vs[samples / 2]
    );
}
