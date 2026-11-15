// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Complete packed SHA compression proofs, including the real PCS opening.
use longfellow_zk::{
    circuits::{
        sha256::Given,
        simd_sha256::{self, Policy},
    },
    compile::algebra::gf2_128::Gf2_128Field as CF,
    core::proto::v2::{CircuitReader, CircuitWriter},
    runtime::{
        algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as F},
        random::{DeterministicRng, RandomEngine},
        v2::{
            proto::polygero::PolygeroConfig,
            simd_sumcheck::{AffineInput, Program},
        },
    },
};
mod support;
use support::memory;
fn main() {
    let started = std::time::Instant::now();
    let flat = simd_sha256::compile(Policy::Products).unwrap();
    eprintln!("Offline circuit: {:.3} ms; input bits/lane={} advice bits/lane={} residuals={} quadratic incidences={}",started.elapsed().as_secs_f64()*1000.,flat.circuit.raw.ninput,flat.additional_bits_per_lane(),flat.circuit.raw.noutput,flat.circuit.raw.layers[0].quadratic.num_terms());
    let (factored, forms) = flat.factored();
    let bytes = CircuitWriter::new(&CF::new()).to_bytes(&factored);
    let (factored, tail) = CircuitReader::new(&F::new()).from_bytes(&bytes).unwrap();
    assert!(tail.is_empty());
    let program = Program::new(
        factored,
        flat.circuit.raw.ninput,
        forms
            .into_iter()
            .map(|a| AffineInput {
                vars: a.vars,
                constant: a.constant,
            })
            .collect(),
        flat.circuit.id,
    )
    .unwrap();
    eprintln!(
        "Packed words={} shared ANDs={} sumcheck rounds={} native cells={}",
        program.input_words(),
        program.products(),
        program.rounds(),
        program.cell_count() - program.input_words()
    );
    let mut rng = DeterministicRng::new(123);
    let given: Vec<_> = (0..128)
        .map(|_| Given {
            input_block: std::array::from_fn(|_| rng.u128() as u32),
            h0: std::array::from_fn(|_| rng.u128() as u32),
        })
        .collect();
    let original = simd_sha256::pack_instances(&given);
    let cfg = PolygeroConfig {
        k: 842,
        s: 10,
        n: 10111,
        t: 64,
    };
    let samples = std::env::var("SHA256_SIMD_REPEATS")
        .unwrap_or("6".into())
        .parse::<usize>()
        .unwrap();
    assert!(samples >= 2);
    println!("sample,prover_ms,verifier_ms,proof_bytes,prover_heap,verifier_heap");
    let (mut ps, mut vs, mut sizes) = (Vec::new(), Vec::new(), Vec::new());
    for i in 0..samples {
        memory::reset_peak();
        let base = memory::get_current_allocated();
        let start = std::time::Instant::now();
        let words = flat
            .advice()
            .evaluate(&original.iter().map(|x| x.to_u128()).collect::<Vec<_>>())
            .unwrap()
            .into_iter()
            .map(E::from)
            .collect();
        let proof = program
            .prove_complete(
                words,
                b"sha256-simd-benchmark",
                cfg,
                &mut DeterministicRng::new(42 + i as u64),
            )
            .unwrap();
        let p = start.elapsed().as_secs_f64() * 1000.;
        let ph = memory::get_peak_allocated().saturating_sub(base);
        memory::reset_peak();
        let verifier_base = memory::get_current_allocated();
        let verifier_start = std::time::Instant::now();
        program
            .verify_complete(&proof, b"sha256-simd-benchmark", cfg)
            .unwrap();
        let v = verifier_start.elapsed().as_secs_f64() * 1000.;
        let vh = memory::get_peak_allocated().saturating_sub(verifier_base);
        println!("{i},{p:.6},{v:.6},{},{ph},{vh}", proof.len());
        if i > 0 {
            ps.push(p);
            vs.push(v);
            sizes.push(proof.len());
        }
    }
    ps.sort_by(f64::total_cmp);
    vs.sort_by(f64::total_cmp);
    sizes.sort();
    let median = |x: &[f64]| (x[(x.len() - 1) / 2] + x[x.len() / 2]) / 2.;
    eprintln!(
        "Median after warmup: prover={:.3} ms verifier={:.3} ms proof={} bytes",
        median(&ps),
        median(&vs),
        sizes[sizes.len() / 2]
    );
}
