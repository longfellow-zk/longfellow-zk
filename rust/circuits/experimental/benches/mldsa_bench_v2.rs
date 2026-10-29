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

//! V2 online timings start with serialized circuits and raw MLDSA inputs.
//! The prover returns serialized proof bytes; the verifier independently decodes
//! its circuit, expands the public key and reads the proof. Outer timers include
//! local setup and cleanup. Offline compilation is reported separately.

use std::time::{Duration, Instant};

use longfellow_zk::{
    circuits,
    circuits::experimental::mldsa::{
        params::{MlDsa44, MlDsa65, MlDsaParams},
        runtime::{reference::decode_public_key, verifier::ConcreteInstance},
    },
    compile,
    compile::algebra::fp24_ext6::CompileFp24Ext6,
    core,
    core::{
        algebra::SupportsU64Conversions,
        proto::{v2::Circuit, FieldID},
    },
    runtime::{
        algebra::{
            fp24_ext6::{RuntimeElement, RuntimeFp24Ext6},
            range_interpolation::CrtInterpolatorFactory,
        },
        proto::{polygero::PolygeroConfig, zk_v2::commitment_layout},
        random::{DeterministicRng, Transcript},
        zk_v2::{ZkContext, ZkProof, ZkProver, ZkVerifier},
    },
};
// These helpers are test/benchmark machinery, not production compiler APIs.
#[path = "support/memory.rs"]
mod memory;
#[path = "../tests/support/mldsa.rs"]
mod support;
#[path = "../tests/all/mldsa_test_vectors.rs"]
mod vectors;

type BenchResult<T> = Result<T, Box<dyn std::error::Error>>;

struct ProverResult {
    proof_bytes: Vec<u8>,
    circuit_load: Duration,
    witness: Duration,
    commit: Duration,
    prove: Duration,
    serialize: Duration,
}

struct VerifierTimings {
    circuit_load: Duration,
    public_inputs: Duration,
    deserialize: Duration,
    verify: Duration,
}

fn read_circuit(bytes: &[u8], field: &RuntimeFp24Ext6) -> BenchResult<Circuit<RuntimeFp24Ext6>> {
    let (circuit, tail) = core::proto::reader::CircuitReader::new(field, FieldID::None)
        .from_bytes_v2(bytes, false)?;
    if !tail.is_empty() {
        return Err("trailing circuit bytes".into());
    }
    Ok(circuit)
}

fn config(circuit: &Circuit<RuntimeFp24Ext6>) -> BenchResult<PolygeroConfig> {
    // Match the Ligero benchmark's ordinary code rate; target 128-bit per-query FS soundness using
    // Hahn openings against the same nominal algebraic budget instead of copying its count.
    let (_, nw, products) = commitment_layout(circuit, &RuntimeFp24Ext6::new());
    circuit.validate_v2()?;
    compile::polygero::tune_mldsa_128(
        nw,
        &products,
        // Keep ordinary rows and arithmetic/remainder interpolation at a
        // 2048-point convolution FFT, then minimize certified proof bytes.
        // Range interpolation no longer pads a response by k+s extra points.
        |p| 2 * p.k - 1 <= 2048 && p.can_interpolate(&CrtInterpolatorFactory),
    )
    .ok_or_else(|| "no supported MLDSA 128-bit FS profile".into())
}

fn prove<P: MlDsaParams>(
    selected_config: PolygeroConfig,
    circuit_bytes: &[u8],
    public_key: &[u8],
    signature: &[u8],
    message: &[u8],
    context: &[u8],
) -> BenchResult<ProverResult> {
    let field = RuntimeFp24Ext6::new();
    let load_start = Instant::now();
    let circuit = read_circuit(circuit_bytes, &field)?;
    let circuit_load = load_start.elapsed();
    let public_count = circuit.raw.npublic_input;
    let witness_start = Instant::now();
    let instance = ConcreteInstance::<P>::new(public_key, signature, message, context)
        .ok_or("invalid MLDSA instance")?;
    let mut inputs = Vec::new();
    instance.push_wires(&field, &mut inputs);
    assert_eq!(inputs.len(), circuit.raw.ninput);
    let witness = witness_start.elapsed();
    let private = inputs.split_off(public_count);
    let prover = ZkProver::new(circuit, selected_config);
    let zk_context = ZkContext {
        f: &field,
        domain: &CrtInterpolatorFactory,
    };
    let mut rng = DeterministicRng::new(42);
    let mut transcript = Transcript::new(b"mldsa-rust-benchmark");
    let commit_start = Instant::now();
    let (commitment, geometry) = prover.commit(private, &zk_context, &mut transcript, &mut rng)?;
    let commit = commit_start.elapsed();
    let prove_start = Instant::now();
    let proof = prover.prove(
        &inputs[..public_count],
        commitment,
        &mut transcript,
        &zk_context,
    )?;
    let prove = prove_start.elapsed();
    let serialize_start = Instant::now();
    let proof_bytes = proof.write(&geometry, &field)?;
    let serialize = serialize_start.elapsed();
    // Only proof bytes and timing data leave this function. All prover state is
    // dropped before the caller stops the complete online prover timer.
    Ok(ProverResult {
        proof_bytes,
        circuit_load,
        witness,
        commit,
        prove,
        serialize,
    })
}

/// Build verifier inputs entirely from the raw public key. No witness or
/// prover-prepared public-input vector is shared with the verifier.
fn public_inputs<P: MlDsaParams>(
    field: &RuntimeFp24Ext6,
    bytes: &[u8],
) -> BenchResult<Vec<RuntimeElement>> {
    let key = decode_public_key::<P>(bytes).ok_or("invalid MLDSA public key")?;
    let mut inputs = Vec::new();
    for polynomial in key.a_hat.iter().flatten() {
        inputs.extend(
            polynomial
                .iter()
                .map(|&x| field.u64_to_element(u64::from(x))),
        );
    }
    for polynomial in key.ntt_t1() {
        inputs.extend(
            polynomial
                .iter()
                .map(|&x| field.u64_to_element(u64::from(x))),
        );
    }
    Ok(inputs)
}

fn verify<P: MlDsaParams>(
    selected_config: PolygeroConfig,
    circuit_bytes: &[u8],
    public_key: &[u8],
    proof_bytes: &[u8],
) -> BenchResult<VerifierTimings> {
    let field = RuntimeFp24Ext6::new();
    let load_start = Instant::now();
    let circuit = read_circuit(circuit_bytes, &field)?;
    let circuit_load = load_start.elapsed();
    let public_start = Instant::now();
    let inputs = public_inputs::<P>(&field, public_key)?;
    let public_inputs = public_start.elapsed();
    if inputs.len() != circuit.raw.npublic_input {
        return Err("public input count mismatch".into());
    }
    let zk_context = ZkContext {
        f: &field,
        domain: &CrtInterpolatorFactory,
    };
    let deserialize_start = Instant::now();
    let mut verifier = ZkVerifier::new(circuit, selected_config, &zk_context)?;
    let geometry = verifier.geometry();
    let mut remaining = proof_bytes;
    let proof = ZkProof::read(&mut remaining, &geometry, &field)?;
    if !remaining.is_empty() {
        return Err("trailing proof bytes".into());
    }
    let deserialize = deserialize_start.elapsed();
    let mut transcript = Transcript::new(b"mldsa-rust-benchmark");
    let verify_start = Instant::now();
    verifier.receive_commitment(&proof, &mut transcript);
    verifier.verify(&inputs, &proof, &mut transcript, &zk_context)?;
    let verify = verify_start.elapsed();
    Ok(VerifierTimings {
        circuit_load,
        public_inputs,
        deserialize,
        verify,
    })
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn run<P: MlDsaParams>(source: &str, marker: &str) {
    let example = vectors::first_cpp_example(source, marker);
    let compile_field = CompileFp24Ext6::new();
    let offline_start = Instant::now();
    let (circuit_bytes, circuit_geometry) =
        if let Some(directory) = std::env::var_os("MLDSA_BENCH_ARCHIVE_DIR") {
            let name = std::any::type_name::<P>().rsplit("::").next().unwrap();
            let path = std::path::PathBuf::from(directory).join(format!("{name}.lfc3"));
            (
                std::fs::read(path).expect("read MLDSA benchmark circuit"),
                None,
            )
        } else {
            let classes = coefficients::from_env(|one, minus_one| {
                core::proto::fixed::CoefficientClasses { one, minus_one }
            });
            let (compiled, geometry, _) =
                support::compile_v2_verifier_with_classes::<P>(&compile_field, classes);
            let segmented = compile::compiler::segment_circuit_v2(&compile_field, &compiled);
            let bytes = core::proto::writer::CircuitWriter::new(&compile_field, FieldID::None)
                .to_bytes_v2(&segmented);
            (bytes, Some(geometry))
        };
    if let Some(directory) = std::env::var_os("MLDSA_BENCH_SAVE_DIR") {
        std::fs::create_dir_all(&directory).unwrap();
        let name = std::any::type_name::<P>().rsplit("::").next().unwrap();
        std::fs::write(
            std::path::PathBuf::from(directory).join(format!("{name}.lfc3")),
            &circuit_bytes,
        )
        .unwrap();
    }
    eprintln!(
        "  Circuit size: raw={} zstd={} bytes",
        circuit_bytes.len(),
        zstd::encode_all(circuit_bytes.as_slice(), 16)
            .unwrap()
            .len()
    );
    let report_field = RuntimeFp24Ext6::new();
    let report_circuit = read_circuit(&circuit_bytes, &report_field).unwrap();
    eprintln!(
        "  Decoded circuit heap: {} bytes",
        report_circuit.heap_bytes()
    );
    let selected_config = config(&report_circuit).unwrap();
    eprintln!(
        "  Term counts [quadratic,linear,constant] x [zero,one,minus_one,other]: {:?}",
        report_circuit.term_class_breakdown(&report_field)
    );
    eprintln!("  Selected Polygero parameters: {selected_config:?}");
    drop(report_circuit);
    let offline_setup = offline_start.elapsed();

    use sha2::Digest;
    eprintln!("  LFC2 SHA-256: {:x}", sha2::Sha256::digest(&circuit_bytes));
    let repeats = std::env::var("MLDSA_BENCH_REPEATS")
        .map(|value| value.parse::<usize>().expect("invalid MLDSA_BENCH_REPEATS"))
        .unwrap_or(1);
    assert!(repeats > 0, "MLDSA_BENCH_REPEATS must be positive");
    for iteration in 0..repeats {
        eprintln!("  Run {}/{}", iteration + 1, repeats);
        let prover_heap = memory::Measurement::start();
        let prover_start = Instant::now();
        let result = prove::<P>(
            selected_config,
            &circuit_bytes,
            &example[1],
            &example[4],
            &example[0],
            &example[2],
        )
        .unwrap();
        let prover_e2e = prover_start.elapsed();
        let prover_peak = prover_heap.finish();
        let verifier_heap = memory::Measurement::start();
        let verifier_start = Instant::now();
        let checked = verify::<P>(
            selected_config,
            &circuit_bytes,
            &example[1],
            &result.proof_bytes,
        )
        .unwrap();
        let verifier_e2e = verifier_start.elapsed();
        let verifier_peak = verifier_heap.finish();

        eprintln!(
            "V2 Polygero {}: {circuit_geometry:?}, LFC3={} bytes",
            std::any::type_name::<P>(),
            circuit_bytes.len()
        );
        eprintln!(
            "  End to end: prover={:.3} ms, verifier={:.3} ms, proof={} bytes",
            ms(prover_e2e),
            ms(verifier_e2e),
            result.proof_bytes.len()
        );
        eprintln!("  Offline circuit preparation: {:.3} ms", ms(offline_setup));
        eprintln!("  Prover subtimings: circuit_load={:.3}, witness={:.3}, commit={:.3}, prove={:.3}, serialize={:.3} ms", ms(result.circuit_load), ms(result.witness), ms(result.commit), ms(result.prove), ms(result.serialize));
        eprintln!("  Verifier subtimings: circuit_load={:.3}, public_inputs={:.3}, deserialize={:.3}, verify={:.3} ms", ms(checked.circuit_load), ms(checked.public_inputs), ms(checked.deserialize), ms(checked.verify));
        if cfg!(feature = "bench-memory") {
            eprintln!(
                "  End-to-end additional peak heap: prover={}, verifier={} bytes",
                prover_peak.additional(),
                verifier_peak.additional()
            );
        }
        // Negative verification is deliberately outside the successful-operation timers.
        let mut different_key = example[1].clone();
        different_key[0] ^= 1;
        assert!(verify::<P>(
            selected_config,
            &circuit_bytes,
            &different_key,
            &result.proof_bytes
        )
        .is_err());
    }
}

fn main() {
    let parameter = std::env::args().nth(1).unwrap_or_else(|| "all".into());
    assert!(
        ["44", "65", "all", "--bench"].contains(&parameter.as_str()),
        "choose 44, 65, or all"
    );
    eprintln!("V2 prototype implementation, rate 1/4 matched to Ligero with tuned openings. Online timings include circuit/proof decoding, input/witness preparation, commitment, serialization, and cleanup as appropriate. Inputs are memory-resident; offline compilation is separate. Allocation tracking: {}", cfg!(feature = "bench-memory"));
    if parameter != "65" {
        run::<MlDsa44>(
            include_str!("../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc"),
            "GetMlDsa44Examples()",
        );
    }
    if parameter != "44" {
        run::<MlDsa65>(
            include_str!("../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc"),
            "GetMlDsa65Examples()",
        );
    }
}

#[path = "../../../benches/support/coefficients.rs"]
mod coefficients;
