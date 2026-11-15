// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use longfellow_zk::{
    core::proto::v2::CircuitWriter,
    mldsa::{
        proto::{BinaryKeccak, KeccakBackend, MlDsa44, MlDsa65, MlDsaParams},
        runtime::{hidden, reference::ConcreteInstance},
        testcases as vectors,
    },
    runtime::random::DeterministicRng,
};
mod support;
use support::memory;
fn run<P: MlDsaParams>(text: &str, marker: &str, backend: KeccakBackend) {
    let e = vectors::first_cpp_example(text, marker);
    let instance = ConcreteInstance::<P>::new(&e[1], &e[4], &e[0], &e[2]).unwrap();
    let compilation_started = std::time::Instant::now();
    let keccak = BinaryKeccak {
        external_permutations: backend != KeccakBackend::Scalar,
        ..BinaryKeccak::default()
    };
    let c = longfellow_zk::mldsa::development_provider::compile_hidden_with_backend::<P>(
        keccak, backend,
    )
    .unwrap();
    eprintln!(
        "hidden ML-DSA {}x{} {} compile_ms={:.3}",
        P::K,
        P::L,
        backend.label(),
        compilation_started.elapsed().as_secs_f64() * 1000.
    );
    for (name, wires, terms, layers) in [
        (
            "binary",
            c.binary.raw.layers.iter().map(|l| l.nw()).sum::<usize>() + c.binary.raw.noutput,
            c.binary
                .raw
                .layers
                .iter()
                .map(|l| l.num_terms())
                .sum::<usize>(),
            c.binary.raw.layers.len(),
        ),
        (
            "arithmetic",
            c.arithmetic
                .raw
                .layers
                .iter()
                .map(|l| l.nw())
                .sum::<usize>()
                + c.arithmetic.raw.noutput,
            c.arithmetic
                .raw
                .layers
                .iter()
                .map(|l| l.num_terms())
                .sum::<usize>(),
            c.arithmetic.raw.layers.len(),
        ),
    ] {
        eprintln!("{name} circuit total_wires={wires} terms={terms} layers={layers}");
    }
    let b = CircuitWriter::new(&longfellow_zk::runtime::algebra::gf2_128::Gf2_128Field::new())
        .to_bytes(&c.binary);
    let arithmetic_archive =
        CircuitWriter::new(&longfellow_zk::runtime::algebra::fp24_ext6::RuntimeFp24Ext6::new())
            .to_bytes(&c.arithmetic);
    let mut archive = b.clone();
    archive.extend(arithmetic_archive);
    eprintln!(
        "scalar_fragments raw={} zstd16={} binary_inputs={} native_inputs={}",
        archive.len(),
        zstd::bulk::compress(&archive, 16).unwrap().len(),
        c.binary.raw.ninput,
        c.arithmetic.raw.ninput
    );
    archive.extend(c.metadata_bytes());
    eprintln!(
        "all_circuit_information raw={} zstd16={} simd_permutations={}",
        archive.len(),
        zstd::bulk::compress(&archive, 16).unwrap().len(),
        c.simd_permutations()
    );
    if let Some(p) = c.simd_program() {
        eprintln!(
            "SIMD products={} source_words={} cells_with_simd_masks={}",
            p.products(),
            p.input_words(),
            p.cell_count()
        );
    }
    if std::env::var_os("MLDSA_BENCH_STATS_ONLY").is_some() {
        return;
    }
    let samples = std::env::var("MLDSA_BENCH_REPEATS")
        .unwrap_or("3".into())
        .parse::<usize>()
        .unwrap();
    assert!(samples >= 2);
    let mut p = vec![];
    let mut v = vec![];
    println!("sample,prover_ms,verifier_ms,proof_bytes,prover_heap,verifier_heap");
    for i in 0..samples {
        memory::reset_peak();
        let base = memory::get_current_allocated();
        let proving_started = std::time::Instant::now();
        let proof = hidden::prove(
            &c,
            &e[1],
            &instance,
            b"hidden benchmark",
            &mut DeterministicRng::new(42 + i as u64),
        )
        .unwrap();
        let pm = proving_started.elapsed().as_secs_f64() * 1000.;
        let proving_peak = memory::get_peak_allocated();
        let prover_heap = proving_peak.saturating_sub(base);
        memory::reset_peak();
        let verifier_base = memory::get_current_allocated();
        let verifying_started = std::time::Instant::now();
        hidden::verify::<P>(&c, b"hidden benchmark", &proof).unwrap();
        let vm = verifying_started.elapsed().as_secs_f64() * 1000.;
        let verifying_peak = memory::get_peak_allocated();
        let verifier_heap = verifying_peak.saturating_sub(verifier_base);
        if cfg!(feature = "bench-memory") {
            eprintln!(
                "sample={i} peak_heap_bytes={}",
                proving_peak.max(verifying_peak).saturating_sub(base)
            );
        }
        println!(
            "{i},{pm:.6},{vm:.6},{},{prover_heap},{verifier_heap}",
            proof.len()
        );
        if i > 0 {
            p.push(pm);
            v.push(vm);
        }
    }
    p.sort_by(f64::total_cmp);
    v.sort_by(f64::total_cmp);
    let median = |a: &[f64]| (a[(a.len() - 1) / 2] + a[a.len() / 2]) / 2.;
    eprintln!(
        "warm median prover_ms={:.6} verifier_ms={:.6}",
        median(&p),
        median(&v)
    );
}
fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let backend = match args.get(1).map(String::as_str).unwrap_or("scalar") {
        "scalar" => KeccakBackend::Scalar,
        "simd" | "permutations" => KeccakBackend::Permutations,
        "rounds" => KeccakBackend::Rounds,
        _ => panic!("hidden Keccak backend must be scalar, simd or rounds"),
    };
    match args.first().map(String::as_str).unwrap_or("44") {
        "44" => run::<MlDsa44>(
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc"
            )),
            "GetMlDsa44Examples()",
            backend,
        ),
        "65" => run::<MlDsa65>(
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc"
            )),
            "GetMlDsa65Examples()",
            backend,
        ),
        _ => panic!("usage: hidden_mldsa 44|65 scalar|permutations|rounds"),
    }
}
