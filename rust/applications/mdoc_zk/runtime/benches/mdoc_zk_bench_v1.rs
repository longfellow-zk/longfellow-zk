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

//! Longfellow v1 / circuit v7 end-to-end benchmark.
//! MDOC_BENCH_ATTRIBUTES selects one to four attributes (default: one).

#[path = "../../../../benches/support/memory.rs"]
mod memory;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use longfellow_zk::{
    compile::algebra::CompileNat,
    core::algebra::Nat,
    mdoc::{
        circuits::parse_test_data,
        v1::{
            decompress_circuits, req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner,
            RequestedAttribute,
        },
    },
    runtime::algebra::{
        fp2::Fp2Field,
        range_interpolation::{
            BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
        },
        SupportsFFT,
    },
};
use memory::{get_current_allocated, get_peak_allocated, reset_peak};

fn hex_id(id: &[u8; 32]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(64);
    for byte in id {
        write!(&mut s, "{byte:02x}").unwrap();
    }
    s
}

fn bench_mdoc_zk_flow(c: &mut Criterion) {
    println!("Allocation tracking: {}", cfg!(feature = "bench-memory"));
    let num_attributes = std::env::var("MDOC_BENCH_ATTRIBUTES")
        .map(|value| {
            value
                .parse::<usize>()
                .expect("invalid MDOC_BENCH_ATTRIBUTES")
        })
        .unwrap_or(1);
    assert!(
        (1..=4).contains(&num_attributes),
        "choose one to four attributes"
    );
    println!("Requested attributes: {num_attributes}");
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&longfellow_zk::mdoc::testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .take(num_attributes)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();

    let mdoc_bytes = longfellow_zk::mdoc::testcases::vectors::TEST_DATA.mdoc;
    let transcript = longfellow_zk::mdoc::testcases::vectors::TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";

    let pubkey_x_string = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pubkey_y_formatted = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );

    let provided = longfellow_zk::mdoc::v1::provider::materialize(7, req_attrs.len()).unwrap();
    let spec = &provided.spec;
    let hash_hex = spec.combined_hash_hex();
    let circuits_lfa1 = longfellow_zk::mdoc::artifacts::load_circuit_lfa1(&hash_hex);
    let (config_hash, config_sig) = longfellow_zk::mdoc::v1::ligero_configs(spec);

    let gf2_runtime = longfellow_zk::runtime::algebra::gf2_128::Gf2_128RuntimeField::new();
    let p256_runtime = longfellow_zk::runtime::algebra::p256::P256Field::new();
    let subfield = longfellow_zk::runtime::algebra::subfield_v1::BinarySubfield::new(
        &longfellow_zk::core::algebra::proto::GF2_16_BASIS_V1,
    );
    let make_interpolator_hash = BinaryInterpolatorFactory::new(&gf2_runtime, &subfield);
    let p256_2 = Fp2Field::new(&p256_runtime);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig =
        QuadraticExtensionFftInterpolatorFactory::new(&p256_runtime, &p256_2, omega, omega_order);

    {
        let (c_sig, c_hash) =
            decompress_circuits(&circuits_lfa1, &p256_runtime, &gf2_runtime).unwrap();

        println!("--------------------------------------------------");
        println!("Circuit Stats (v7 Official Circuit):");
        let mut decompressed = Vec::new();
        zstd::stream::copy_decode(std::io::Cursor::new(&circuits_lfa1), &mut decompressed)
            .expect("decompress");
        println!(
            "  Circuit Sizes: zstd-{}={} bytes, segmented (no zstd)={} bytes",
            longfellow_zk::mdoc::circuits::config::K_ZSTD_LEVEL,
            circuits_lfa1.len(),
            decompressed.len()
        );
        println!("  Sig Circuit ID:  {}", hex_id(&c_sig.id));
        println!("  Hash Circuit ID: {}", hex_id(&c_hash.id));
        println!("  Overall Spec Hash: {}", hash_hex);
        println!(
            "  Hash Circuit: inputs={}, pub_inputs={}, outputs={}, layers={}, wires={}, terms={}",
            c_hash.raw.ninput,
            c_hash.raw.npublic_input,
            c_hash.raw.noutput,
            c_hash.raw.layers.len(),
            c_hash
                .raw
                .layers
                .iter()
                .map(longfellow_zk::core::proto::layer::Layer::nw)
                .sum::<usize>()
                - c_hash.raw.ninput
                + c_hash.raw.noutput,
            c_hash
                .raw
                .layers
                .iter()
                .map(longfellow_zk::core::proto::layer::Layer::num_terms)
                .sum::<usize>()
        );
        let (count_w_hash, total_q_hash) =
            longfellow_zk::runtime::proto::zk_v1::witness_and_constraint_count(&c_hash);
        let param_hash = longfellow_zk::runtime::ligero::param::LigeroParam::try_new(
            count_w_hash,
            total_q_hash,
            config_hash,
            &make_interpolator_hash,
        )
        .unwrap();
        println!(
            "  Hash Ligero:  block={}, dblock={}, block_enc={}, nrow={}, mc_pathlen={}",
            param_hash.block,
            param_hash.dblock,
            param_hash.block_enc,
            param_hash.geom.nrow,
            param_hash.geom.mc_pathlen
        );
        println!(
            "  Sig Circuit:  inputs={}, pub_inputs={}, outputs={}, layers={}, wires={}, terms={}",
            c_sig.raw.ninput,
            c_sig.raw.npublic_input,
            c_sig.raw.noutput,
            c_sig.raw.layers.len(),
            c_sig
                .raw
                .layers
                .iter()
                .map(longfellow_zk::core::proto::layer::Layer::nw)
                .sum::<usize>()
                - c_sig.raw.ninput
                + c_sig.raw.noutput,
            c_sig
                .raw
                .layers
                .iter()
                .map(longfellow_zk::core::proto::layer::Layer::num_terms)
                .sum::<usize>()
        );
        let (count_w_sig, total_q_sig) =
            longfellow_zk::runtime::proto::zk_v1::witness_and_constraint_count(&c_sig);
        let param_sig = longfellow_zk::runtime::ligero::param::LigeroParam::try_new(
            count_w_sig,
            total_q_sig,
            config_sig,
            &make_interpolator_sig,
        )
        .unwrap();
        println!(
            "  Sig Ligero:   block={}, dblock={}, block_enc={}, nrow={}, mc_pathlen={}",
            param_sig.block,
            param_sig.dblock,
            param_sig.block_enc,
            param_sig.geom.nrow,
            param_sig.geom.mc_pathlen
        );
    }
    println!(
        "Compressed circuits (concatenated) size: {} bytes",
        circuits_lfa1.len()
    );

    // Dry-run prover once to get proof size and heap memory stats
    let baseline = get_current_allocated();
    reset_peak();

    let mut rng_lfa1 = longfellow_zk::runtime::random::DeterministicRng::new(42);
    let zkproof_lfa1 = run_mdoc_prover_inner(
        spec,
        &circuits_lfa1,
        mdoc_bytes,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &mut rng_lfa1,
    )
    .unwrap();

    let mut baseline_heap = 0;
    let mut baseline_peak_heap = 0;

    let heap = get_current_allocated();
    if heap > baseline {
        baseline_heap = heap - baseline;
    }

    let peak = get_peak_allocated();
    if peak > baseline {
        baseline_peak_heap = peak - baseline;
    }

    let baseline_ver = get_current_allocated();
    reset_peak();
    run_mdoc_verifier_inner(
        spec,
        &circuits_lfa1,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &zkproof_lfa1,
    )
    .unwrap();
    let mut baseline_heap_ver = 0;
    let mut baseline_peak_heap_ver = 0;
    let heap_ver = get_current_allocated();
    if heap_ver > baseline_ver {
        baseline_heap_ver = heap_ver - baseline_ver;
    }
    let peak_ver = get_peak_allocated();
    if peak_ver > baseline_ver {
        baseline_peak_heap_ver = peak_ver - baseline_ver;
    }

    println!("--------------------------------------------------");
    println!("Baseline Circuit Memory Stats (Longfellow v1, circuit v7, LFA1 archive):");
    println!("  Proof Size: {} bytes", zkproof_lfa1.len());
    if cfg!(feature = "bench-memory") {
        println!("  Prover Net Heap Memory: {baseline_heap} bytes");
        println!("  Prover Peak Heap Memory: {baseline_peak_heap} bytes");
        println!("  Verifier Net Heap Memory: {baseline_heap_ver} bytes");
        println!("  Verifier Peak Heap Memory: {baseline_peak_heap_ver} bytes");
    } else {
        println!("  Heap tracking disabled; enable bench-memory for a separate memory run.");
    }
    println!("--------------------------------------------------");

    let circuits_lfa2 = longfellow_zk::mdoc::artifacts::load_circuit_lfa2(&hash_hex);

    let baseline_lfa2 = get_current_allocated();
    reset_peak();
    let mut rng_lfa2 = longfellow_zk::runtime::random::DeterministicRng::new(42);
    let zkproof_lfa2 = run_mdoc_prover_inner(
        spec,
        &circuits_lfa2,
        mdoc_bytes,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &mut rng_lfa2,
    )
    .unwrap();
    let mut baseline_heap_lfa2 = 0;
    let mut baseline_peak_heap_lfa2 = 0;
    let heap_lfa2 = get_current_allocated();
    if heap_lfa2 > baseline_lfa2 {
        baseline_heap_lfa2 = heap_lfa2 - baseline_lfa2;
    }
    let peak_lfa2 = get_peak_allocated();
    if peak_lfa2 > baseline_lfa2 {
        baseline_peak_heap_lfa2 = peak_lfa2 - baseline_lfa2;
    }

    let baseline_ver_lfa2 = get_current_allocated();
    reset_peak();
    run_mdoc_verifier_inner(
        spec,
        &circuits_lfa2,
        &pubkey_x_string,
        &pubkey_y_formatted,
        transcript,
        &req_attrs,
        now,
        doc_type,
        &zkproof_lfa2,
    )
    .unwrap();
    let mut baseline_heap_ver_lfa2 = 0;
    let mut baseline_peak_heap_ver_lfa2 = 0;
    let heap_ver_lfa2 = get_current_allocated();
    if heap_ver_lfa2 > baseline_ver_lfa2 {
        baseline_heap_ver_lfa2 = heap_ver_lfa2 - baseline_ver_lfa2;
    }
    let peak_ver_lfa2 = get_peak_allocated();
    if peak_ver_lfa2 > baseline_ver_lfa2 {
        baseline_peak_heap_ver_lfa2 = peak_ver_lfa2 - baseline_ver_lfa2;
    }

    println!("--------------------------------------------------");
    println!("Baseline Circuit Memory Stats (Longfellow v1, circuit v7, LFA2 archive):");
    println!("  Proof Size: {} bytes", zkproof_lfa2.len());
    if cfg!(feature = "bench-memory") {
        println!("  Prover Net Heap Memory: {baseline_heap_lfa2} bytes");
        println!("  Prover Peak Heap Memory: {baseline_peak_heap_lfa2} bytes");
        println!("  Verifier Net Heap Memory: {baseline_heap_ver_lfa2} bytes");
        println!("  Verifier Peak Heap Memory: {baseline_peak_heap_ver_lfa2} bytes");
    } else {
        println!("  Heap tracking disabled; enable bench-memory for a separate memory run.");
    }
    println!("--------------------------------------------------");

    let mut group = c.benchmark_group(format!(
        "longfellow_v1_circuit_v7/{num_attributes}_attributes"
    ));
    group.sample_size(10);
    group.bench_function("prove_longfellow_v1_circuit_v7_lfa1", |b| {
        b.iter(|| {
            let mut rng = longfellow_zk::runtime::random::DeterministicRng::new(42);
            let zkproof = run_mdoc_prover_inner(
                black_box(spec),
                black_box(&circuits_lfa1),
                black_box(mdoc_bytes),
                black_box(&pubkey_x_string),
                black_box(&pubkey_y_formatted),
                black_box(transcript),
                black_box(&req_attrs),
                black_box(now),
                black_box(doc_type),
                &mut rng,
            )
            .unwrap();
            black_box(zkproof);
        });
    });
    group.bench_function("verify_longfellow_v1_circuit_v7_lfa1", |b| {
        b.iter(|| {
            let verify_res = run_mdoc_verifier_inner(
                black_box(spec),
                black_box(&circuits_lfa1),
                black_box(&pubkey_x_string),
                black_box(&pubkey_y_formatted),
                black_box(transcript),
                black_box(&req_attrs),
                black_box(now),
                black_box(doc_type),
                black_box(&zkproof_lfa1),
            );
            assert!(verify_res.is_ok());
        });
    });
    group.bench_function("prove_longfellow_v1_circuit_v7_lfa2", |b| {
        b.iter(|| {
            let mut rng = longfellow_zk::runtime::random::DeterministicRng::new(42);
            let zkproof = run_mdoc_prover_inner(
                black_box(spec),
                black_box(&circuits_lfa2),
                black_box(mdoc_bytes),
                black_box(&pubkey_x_string),
                black_box(&pubkey_y_formatted),
                black_box(transcript),
                black_box(&req_attrs),
                black_box(now),
                black_box(doc_type),
                &mut rng,
            )
            .unwrap();
            black_box(zkproof);
        });
    });
    group.bench_function("verify_longfellow_v1_circuit_v7_lfa2", |b| {
        b.iter(|| {
            let verify_res = run_mdoc_verifier_inner(
                black_box(spec),
                black_box(&circuits_lfa2),
                black_box(&pubkey_x_string),
                black_box(&pubkey_y_formatted),
                black_box(transcript),
                black_box(&req_attrs),
                black_box(now),
                black_box(doc_type),
                black_box(&zkproof_lfa2),
            );
            assert!(verify_res.is_ok());
        });
    });
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
