// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Complete ML-DSA proofs with public-key projections across two fields.
use longfellow_zk::{
    mldsa::{
        development_provider::prepare_public_with_backend,
        proto::{BinaryKeccak, KeccakBackend, MlDsa44, MlDsa65, MlDsaParams},
        runtime::{self, reference::ConcreteInstance},
        testcases as vectors,
    },
    runtime::random::DeterministicRng,
};
mod support;
use support::memory;
fn number_option<T: std::str::FromStr>(name: &str, default: T) -> T {
    match std::env::var_os(name) {
        None => default,
        Some(value) => value
            .to_str()
            .unwrap_or_else(|| panic!("{name} must be UTF-8"))
            .parse()
            .unwrap_or_else(|_| panic!("{name} must be an integer")),
    }
}
fn bool_option(name: &str, default: bool) -> bool {
    match std::env::var_os(name) {
        None => default,
        Some(value) => match value.to_str() {
            Some("0" | "false") => false,
            Some("1" | "true") => true,
            _ => panic!("{name} must be 0, 1, false or true"),
        },
    }
}
fn run<P: MlDsaParams>(source: &str, marker: &str) {
    let example = vectors::first_cpp_example(source, marker);
    let compilation_started = std::time::Instant::now();
    let backend = match std::env::var("MLDSA_SHAKE_BACKEND")
        .as_deref()
        .unwrap_or("scalar")
    {
        "scalar" => KeccakBackend::Scalar,
        "permutations" => KeccakBackend::Permutations,
        "rounds" => KeccakBackend::Rounds,
        _ => panic!("MLDSA_SHAKE_BACKEND must be scalar, permutations or rounds"),
    };
    let defaults = BinaryKeccak::default();
    let keccak = BinaryKeccak {
        external_permutations: backend != KeccakBackend::Scalar,
        rounds_per_slice: number_option("MLDSA_ROUNDS_PER_SLICE", defaults.rounds_per_slice),
        theta_mode: number_option("MLDSA_THETA_MODE", defaults.theta_mode),
        materialize_chi: bool_option("MLDSA_MATERIALIZE_CHI", defaults.materialize_chi),
        expanded_chi: bool_option("MLDSA_EXPANDED_CHI", defaults.expanded_chi),
        packed_checkpoints: bool_option("MLDSA_PACKED_CHECKPOINTS", defaults.packed_checkpoints),
    };
    let archive = prepare_public_with_backend::<P>(keccak, backend);
    eprintln!(
        "Keccak layout: {} backend={}",
        archive.keccak.label(),
        backend.label()
    );
    eprintln!(
        "Offline compilation/preparation: {:.3} ms",
        compilation_started.elapsed().as_secs_f64() * 1000.
    );
    eprintln!(
        "Circuit bytes: binary={}; profile={:?}",
        archive.binary.len(),
        archive.config
    );
    memory::reset_peak();
    let decode_heap_base = memory::get_current_allocated();
    let decoded = archive.load();
    eprintln!(
        "Decoded circuit heap: {} bytes",
        memory::get_current_allocated().saturating_sub(decode_heap_base)
    );
    let shape = report(&decoded.binary);
    eprintln!(
        "binary: inputs={} public={} layers={} wires={} terms={} rounds={}",
        shape[0], shape[1], shape[2], shape[3], shape[4], shape[5]
    );
    drop(decoded);
    let samples = std::env::var("MLDSA_BENCH_REPEATS")
        .unwrap_or("9".into())
        .parse::<usize>()
        .unwrap();
    assert!(samples >= 2);
    println!("sample,prover_ms,verifier_ms,proof_bytes,prover_heap,verifier_heap");
    let (mut pt, mut vt, mut sizes) = (Vec::new(), Vec::new(), Vec::new());
    for i in 0..samples {
        memory::reset_peak();
        let proving_heap_base = memory::get_current_allocated();
        let proving_started = std::time::Instant::now();
        let proving_circuit = archive.load();
        let instance =
            ConcreteInstance::<P>::new(&example[1], &example[4], &example[0], &example[2]).unwrap();
        let proof = runtime::prove(
            &proving_circuit,
            &example[1],
            &instance,
            b"mldsa-benchmark",
            &mut DeterministicRng::new(42 + i as u64),
        )
        .unwrap();
        drop((proving_circuit, instance));
        let p = proving_started.elapsed().as_secs_f64() * 1000.;
        let ph = memory::get_peak_allocated().saturating_sub(proving_heap_base);
        memory::reset_peak();
        let verifying_heap_base = memory::get_current_allocated();
        let verifying_started = std::time::Instant::now();
        let verifying_circuit = archive.load();
        runtime::verify::<P>(&verifying_circuit, &example[1], b"mldsa-benchmark", &proof).unwrap();
        drop(verifying_circuit);
        let v = verifying_started.elapsed().as_secs_f64() * 1000.;
        let vh = memory::get_peak_allocated().saturating_sub(verifying_heap_base);
        println!("{i},{p:.6},{v:.6},{},{ph},{vh}", proof.len());
        if i > 0 {
            pt.push(p);
            vt.push(v);
            sizes.push(proof.len());
        }
    }
    pt.sort_by(f64::total_cmp);
    vt.sort_by(f64::total_cmp);
    sizes.sort();
    let median = |v: &[f64]| (v[(v.len() - 1) / 2] + v[v.len() / 2]) / 2.;
    eprintln!(
        "Median after warmup: prover={:.3} ms verifier={:.3} ms proof={} bytes",
        median(&pt),
        median(&vt),
        sizes[sizes.len() / 2]
    );
}
fn report<F: longfellow_zk::core::algebra::SerializableField>(
    c: &longfellow_zk::core::proto::v2::Circuit<F>,
) -> [usize; 6] {
    [
        c.raw.ninput,
        c.raw.npublic_input,
        c.raw.layers.len(),
        c.raw.layers.iter().map(|l| l.nw).sum::<usize>() + c.raw.noutput - c.raw.ninput,
        c.raw.layers.iter().map(|l| l.num_terms()).sum(),
        c.raw.layers.iter().map(|l| l.logw).sum(),
    ]
}
fn main() {
    match std::env::args().nth(1).as_deref().unwrap_or("44") {
        "44" => run::<MlDsa44>(
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc"
            )),
            "GetMlDsa44Examples()",
        ),
        "65" => run::<MlDsa65>(
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc"
            )),
            "GetMlDsa65Examples()",
        ),
        _ => panic!("choose 44 or 65"),
    }
}
