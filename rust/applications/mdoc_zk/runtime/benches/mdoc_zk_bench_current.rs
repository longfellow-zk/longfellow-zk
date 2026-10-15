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

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::Ordering,
};

use compile_algebra::CompileNat;
use core_algebra::Nat;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use mdoc_zk_circuits::parse_test_data;
use mdoc_zk_runtime::{
    decompress_circuits, req_attr, run_mdoc_verifier_inner, RequestedAttribute,
};
use runtime_algebra::{
    fp2::Fp2Field,
    lch14_reed_solomon::Lch14InterpolatorFactory,
    mem::{ALLOCATED, PEAK},
    reed_solomon::FftInterpolatorFactory,
    SupportsFFT,
};

struct TrackingAllocator;

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        if !ptr.is_null() {
            let size = layout.size();
            let prev = ALLOCATED.fetch_add(size, Ordering::SeqCst);
            let current = prev + size;
            loop {
                let current_peak = PEAK.load(Ordering::SeqCst);
                if current <= current_peak {
                    break;
                }
                if PEAK
                    .compare_exchange_weak(
                        current_peak,
                        current,
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                    )
                    .is_ok()
                {
                    break;
                }
            }
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
        ALLOCATED.fetch_sub(layout.size(), Ordering::SeqCst);
    }
}

#[global_allocator]
static ALLOC: TrackingAllocator = TrackingAllocator;

fn reset_peak() {
    let current = ALLOCATED.load(Ordering::SeqCst);
    PEAK.store(current, Ordering::SeqCst);
}

fn get_peak_allocated() -> usize {
    PEAK.load(Ordering::SeqCst)
}

fn get_current_allocated() -> usize {
    ALLOCATED.load(Ordering::SeqCst)
}

fn hex_id(id: &[u8; 32]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(64);
    for byte in id {
        write!(&mut s, "{byte:02x}").unwrap();
    }
    s
}

fn bench_mdoc_zk_flow(c: &mut Criterion) {
    use mdoc_zk_runtime::{req_pnym, run_mdoc_prover_inner_ext};

    let gf2_runtime = runtime_algebra::gf2_128::Gf2_128RuntimeField::new();
    let p256_runtime = runtime_algebra::p256::P256Field::new();
    let subfield =
        runtime_algebra::subfield::BinarySubfield::new(&core_algebra::proto::GF2_16_BASIS_V1);
    let make_interpolator_hash = Lch14InterpolatorFactory::new(&gf2_runtime, &subfield);
    let p256_2 = Fp2Field::new(&p256_runtime);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        FftInterpolatorFactory::new(&p256_runtime, &p256_2, omega, omega_order);

    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let all_req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();
    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let pnym_data = &mdoc_zk_testcases::vectors::PNYM_SEED_MDOC;
    let pnym_req = vec![req_pnym(
        "org.iso.18013.5.1",
        b"verifier.example.org/relying-party-session-2026",
    )];

    struct BenchCase<'a> {
        label: &'static str,
        num_attrs: usize,
        pnym: bool,
        mdoc_bytes: &'a [u8],
        pkx: &'a str,
        pky: &'a str,
        transcript: &'a [u8],
        req_attrs: Vec<RequestedAttribute>,
        now: &'a str,
        doc_type: &'a str,
    }

    let cases = [
        BenchCase {
            label: "v8_1attr",
            num_attrs: 1,
            pnym: false,
            mdoc_bytes: mdoc_zk_testcases::vectors::TEST_DATA.mdoc,
            pkx: &pubkey_x_string,
            pky: &pubkey_y_formatted,
            transcript: mdoc_zk_testcases::vectors::TEST_DATA.transcript,
            req_attrs: vec![all_req_attrs[0].clone()],
            now,
            doc_type: "org.iso.18013.5.1.mDL",
        },
        BenchCase {
            label: "v8_4attr",
            num_attrs: 4,
            pnym: false,
            mdoc_bytes: mdoc_zk_testcases::vectors::TEST_DATA.mdoc,
            pkx: &pubkey_x_string,
            pky: &pubkey_y_formatted,
            transcript: mdoc_zk_testcases::vectors::TEST_DATA.transcript,
            req_attrs: all_req_attrs.iter().take(2).cloned().collect(),
            now,
            doc_type: "org.iso.18013.5.1.mDL",
        },
        BenchCase {
            label: "v8_0attr_pnym",
            num_attrs: 0,
            pnym: true,
            mdoc_bytes: pnym_data.mdoc,
            pkx: pnym_data.pkx,
            pky: pnym_data.pky,
            transcript: pnym_data.transcript,
            req_attrs: pnym_req,
            now: pnym_data.now,
            doc_type: pnym_data.doc_type,
        },
    ];

    let mut group = c.benchmark_group("integration_current");
    group.sample_size(10);

    for case in &cases {
        let provided = mdoc_zk_runtime::provider::materialize(
            mdoc_zk_runtime::CURRENT_VERSION,
            case.num_attrs,
            case.pnym,
        )
        .unwrap();
        let spec = &provided.spec;
        let circuits = &provided.compressed;
        let (config_hash, config_sig) = mdoc_zk_runtime::ligero_configs(spec);

        let (c_sig, c_hash) = decompress_circuits(circuits, &p256_runtime, &gf2_runtime).unwrap();

        println!("==================================================");
        println!(
            "Circuit Stats [{}] (version={}, num_attributes={}, pnym={}):",
            case.label, spec.version, spec.num_attributes, spec.pnym
        );
        let mut decompressed = Vec::new();
        zstd::stream::copy_decode(std::io::Cursor::new(circuits), &mut decompressed)
            .expect("decompress");
        println!(
            "  Circuit Sizes: zstd-{}={} bytes, segmented (no zstd)={} bytes",
            mdoc_zk_circuits::config::K_ZSTD_LEVEL,
            circuits.len(),
            decompressed.len()
        );
        println!("  Overall Spec Hash: {}", spec.combined_hash_hex());
        println!("  Sig Circuit ID:    {}", hex_id(&c_sig.id));
        println!("  Hash Circuit ID:   {}", hex_id(&c_hash.id));

        println!(
            "  Hash Circuit: inputs={}, pub_inputs={}, subfield_boundary={}, outputs={}, layers={}, wires={}, terms={}",
            c_hash.raw.ninput,
            c_hash.raw.npublic_input,
            c_hash.raw.subfield_boundary,
            c_hash.raw.noutput,
            c_hash.raw.layers.len(),
            c_hash
                .raw
                .layers
                .iter()
                .map(core_proto::layer::Layer::nw)
                .sum::<usize>()
                - c_hash.raw.ninput
                + c_hash.raw.noutput,
            c_hash
                .raw
                .layers
                .iter()
                .map(core_proto::layer::Layer::num_terms)
                .sum::<usize>(),
        );
        let (count_w_hash, total_q_hash) = runtime_proto::witness_and_constraint_count(&c_hash);
        let param_hash = runtime_ligero::param::LigeroParam::try_new(
            count_w_hash,
            total_q_hash,
            config_hash,
            &make_interpolator_hash,
        )
        .unwrap();
        println!(
            "  Hash Ligero:  witnesses={}, quads={}, block={}, dblock={}, block_enc={}, nrow={}, mc_pathlen={}",
            count_w_hash,
            total_q_hash,
            param_hash.block,
            param_hash.dblock,
            param_hash.block_enc,
            param_hash.geom.nrow,
            param_hash.geom.mc_pathlen
        );
        println!(
            "  Sig Circuit:  inputs={}, pub_inputs={}, subfield_boundary={}, outputs={}, layers={}, wires={}, terms={}",
            c_sig.raw.ninput,
            c_sig.raw.npublic_input,
            c_sig.raw.subfield_boundary,
            c_sig.raw.noutput,
            c_sig.raw.layers.len(),
            c_sig
                .raw
                .layers
                .iter()
                .map(core_proto::layer::Layer::nw)
                .sum::<usize>()
                - c_sig.raw.ninput
                + c_sig.raw.noutput,
            c_sig
                .raw
                .layers
                .iter()
                .map(core_proto::layer::Layer::num_terms)
                .sum::<usize>(),
        );
        let (count_w_sig, total_q_sig) = runtime_proto::witness_and_constraint_count(&c_sig);
        let param_sig = runtime_ligero::param::LigeroParam::try_new(
            count_w_sig,
            total_q_sig,
            config_sig,
            &make_interpolator_sig,
        )
        .unwrap();
        println!(
            "  Sig Ligero:   witnesses={}, quads={}, block={}, dblock={}, block_enc={}, nrow={}, mc_pathlen={}",
            count_w_sig,
            total_q_sig,
            param_sig.block,
            param_sig.dblock,
            param_sig.block_enc,
            param_sig.geom.nrow,
            param_sig.geom.mc_pathlen
        );

        // Dry-run prover once to get proof size and heap memory stats
        let baseline = get_current_allocated();
        reset_peak();

        let mut dry_rng = runtime_random::DeterministicRng::new(42);
        let (dry_zkproof, resolved_attrs) = run_mdoc_prover_inner_ext(
            spec,
            circuits,
            case.mdoc_bytes,
            case.pkx,
            case.pky,
            case.transcript,
            &case.req_attrs,
            case.now,
            case.doc_type,
            &mut dry_rng,
        )
        .unwrap();

        let baseline_heap = get_current_allocated().saturating_sub(baseline);
        let baseline_peak_heap = get_peak_allocated().saturating_sub(baseline);

        let baseline_ver = get_current_allocated();
        reset_peak();
        run_mdoc_verifier_inner(
            spec,
            circuits,
            case.pkx,
            case.pky,
            case.transcript,
            &resolved_attrs,
            case.now,
            case.doc_type,
            &dry_zkproof,
        )
        .unwrap();
        let baseline_heap_ver = get_current_allocated().saturating_sub(baseline_ver);
        let baseline_peak_heap_ver = get_peak_allocated().saturating_sub(baseline_ver);

        println!("  Proof Size: {} bytes", dry_zkproof.len());
        println!("  Prover Net Heap Memory:    {baseline_heap} bytes");
        println!("  Prover Peak Heap Memory:   {baseline_peak_heap} bytes");
        println!("  Verifier Net Heap Memory:  {baseline_heap_ver} bytes");
        println!("  Verifier Peak Heap Memory: {baseline_peak_heap_ver} bytes");

        group.bench_function(format!("prove_{}", case.label), |b| {
            b.iter(|| {
                let mut rng = runtime_random::DeterministicRng::new(42);
                let (zkproof, _) = run_mdoc_prover_inner_ext(
                    black_box(spec),
                    black_box(circuits),
                    black_box(case.mdoc_bytes),
                    black_box(case.pkx),
                    black_box(case.pky),
                    black_box(case.transcript),
                    black_box(&case.req_attrs),
                    black_box(case.now),
                    black_box(case.doc_type),
                    &mut rng,
                )
                .unwrap();
                black_box(zkproof);
            });
        });
        group.bench_function(format!("verify_{}", case.label), |b| {
            b.iter(|| {
                let verify_res = run_mdoc_verifier_inner(
                    black_box(spec),
                    black_box(circuits),
                    black_box(case.pkx),
                    black_box(case.pky),
                    black_box(case.transcript),
                    black_box(&resolved_attrs),
                    black_box(case.now),
                    black_box(case.doc_type),
                    black_box(&dry_zkproof),
                );
                assert!(verify_res.is_ok());
            });
        });
    }
    group.finish();
    print_memory_stats();
}

fn print_memory_stats() {
    if let Ok(status) = std::fs::read_to_string("/proc/self/status") {
        println!("Process OS Memory Stats (Peak/HWM):");
        for line in status.lines() {
            if line.starts_with("VmPeak:") || line.starts_with("VmHWM:") {
                println!("  {line}");
            }
        }
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        .measurement_time(std::time::Duration::from_millis(100))
        .warm_up_time(std::time::Duration::from_millis(100))
        .sample_size(10);
    targets = bench_mdoc_zk_flow
);
criterion_main!(benches);
