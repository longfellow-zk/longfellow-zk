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

use super::mldsa_test_vectors::first_cpp_example;
use circuits_bitvec::{BitvecIO, BitvecLogic};

use circuits_experimental::mldsa::{
    algebra::{CompileFp24Ext6, RuntimeFp24Ext6, SERIALIZED_SIZE},
    params::{MlDsa44, MlDsa65, MlDsaParams},
    shake::slice_period,
    verifier::{ConcreteInstance, MlDsaVerifier, PublicKeyW, SignatureW, VerificationWitness},
};
use compile_eval::{CircuitGeometry, FieldID};
use core_algebra::{AlgebraicField, SerializableField};
use runtime_algebra::Subfield;
use runtime_random::{DeterministicRng, Transcript};

#[path = "../../../../experiments/mldsa/morton.rs"]
mod morton_analysis;

// Keep analysis, evaluation, and proof benchmarks on exactly the same circuit.
// The public input is the expanded key; mu and the signature are private inputs.
fn compile_verifier<P: MlDsaParams>(
    field: &CompileFp24Ext6,
) -> (
    core_proto::circuit::Circuit<CompileFp24Ext6>,
    CircuitGeometry,
    compile_compiler::CircuitDebugSymbols,
) {
    compile_compiler::compile(field, |logic| {
        let bitvec = BitvecLogic::new(&logic);
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let public_key = PublicKeyW::input::<P>(&logic, &bitvec, &mut position);
        let public_input_count = position;
        let signature = SignatureW::input::<P>(&logic, &bitvec, &mut position);
        let witness = VerificationWitness::input::<P>(&logic, &bitvec, &mut position);
        let byte_io = BitvecIO::new(&bitvec);
        let mu: Vec<_> = (0..64).map(|_| byte_io.next(&mut position)).collect();
        let verifier = MlDsaVerifier::<_, P>::new(&logic);
        (
            verifier.assert_valid_signature_on_mu(&public_key, &signature, &mu, &witness),
            public_input_count,
            position,
        )
    })
}

#[test]
#[ignore = "offline component traversal and encoding experiment"]
fn analyze_mldsa44_morton() {
    assert_eq!(slice_period(), 6);
    let field = CompileFp24Ext6::new();
    let (circuit, geometry, symbols) = compile_verifier::<MlDsa44>(&field);
    println!("GEOMETRY {geometry:?}");
    morton_analysis::analyze("mldsa44_p6", &field, &circuit, &symbols, FieldID::None);
}

#[test]
#[ignore = "offline fixed-geometry traversal sweep for MLDSA and mdoc"]
fn analyze_traversal_sweep() {
    assert_eq!(slice_period(), 6);
    assert!(std::env::var_os("MORTON_ORDER_SWEEP").is_some());
    let dataset = std::env::var("SWEEP_DATASET").expect("set SWEEP_DATASET");
    match dataset.as_str() {
        "mldsa44" | "mldsa65" => {
            let f = CompileFp24Ext6::new();
            let (c, g, s) = if dataset == "mldsa44" {
                compile_verifier::<MlDsa44>(&f)
            } else {
                compile_verifier::<MlDsa65>(&f)
            };
            println!("GEOMETRY {dataset} {g:?}");
            morton_analysis::analyze(&dataset, &f, &c, &s, FieldID::None);
        }
        "mdoc_sig" => {
            let f = compile_algebra::p256::P256Field::new();
            let (c, g, s) = mdoc_zk_compile::mdoc_zk_circuits_signature(&f);
            println!("GEOMETRY {dataset} {g:?}");
            morton_analysis::analyze(&dataset, &f, &c, &s, FieldID::P256);
        }
        name if name.starts_with("mdoc_hash") => {
            let n: usize = name.trim_start_matches("mdoc_hash").parse().unwrap();
            assert!((1..=4).contains(&n));
            let f = compile_algebra::gf2_128::Gf2_128Field::new();
            let (c, g, s) = mdoc_zk_compile::mdoc_zk_circuits_hash(&f, n);
            println!("GEOMETRY {dataset} {g:?}");
            morton_analysis::analyze(&dataset, &f, &c, &s, FieldID::Gf2_128);
        }
        _ => panic!("unknown dataset {dataset}"),
    }
}

#[test]
#[ignore = "end-to-end mdoc proof using saved offline reordered circuits"]
fn validate_mdoc_traversal() {
    use core_algebra::Nat;
    use mdoc_zk_runtime::{req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner};
    let directory = std::env::var("SWEEP_SAVE_DIR").unwrap();
    let policy = std::env::var("SWEEP_POLICY").unwrap();
    let n: usize = std::env::var("SWEEP_ATTRS").unwrap().parse().unwrap();
    assert!((1..=4).contains(&n));
    let load = |dataset: &str| {
        std::fs::read(std::path::Path::new(&directory).join(format!("{dataset}--{policy}.lfc2")))
            .unwrap()
    };
    let sig_bytes = load("mdoc_sig");
    let hash_bytes = load(&format!("mdoc_hash{n}"));
    let p256 = compile_algebra::p256::P256Field::new();
    let gf2 = compile_algebra::gf2_128::Gf2_128Field::new();
    let (sig, tail) = core_proto::reader::CircuitReader::new(&p256, FieldID::P256)
        .from_bytes_lfc2(&sig_bytes, true)
        .unwrap();
    assert!(tail.is_empty());
    let (hash, tail) = core_proto::reader::CircuitReader::new(&gf2, FieldID::Gf2_128)
        .from_bytes_lfc2(&hash_bytes, true)
        .unwrap();
    assert!(tail.is_empty());
    let (original_sig, _, _) = mdoc_zk_compile::mdoc_zk_circuits_signature(&p256);
    morton_analysis::assert_same_terms(&p256, &original_sig, &sig);
    drop(original_sig);
    let (original_hash, _, _) = mdoc_zk_compile::mdoc_zk_circuits_hash(&gf2, n);
    morton_analysis::assert_same_terms(&gf2, &original_hash, &hash);
    drop(original_hash);
    let mut builder = core_proto::archive::CircuitArchiveBuilder::new();
    builder.set_circuit_version(mdoc_zk_circuits::CURRENT_VERSION as u32);
    builder.add_entry("sig", sig.id, sig_bytes);
    builder.add_entry("hash", hash.id, hash_bytes);
    let archive = builder.build();
    let mut spec = mdoc_zk_runtime::CURRENT_ZK_SPECS[n - 1];
    spec.combined_hash = archive.combined_id;
    let bytes = archive.to_bytes();
    // Match the production archive compressor (streaming, unknown source size).
    let compressed = zstd::encode_all(&bytes[..], 16).unwrap();
    println!(
        "TRAVERSAL_ARCHIVE attrs={n} policy={policy} raw={} zstd16={} zstd22={} bulk_zstd16={}",
        bytes.len(),
        compressed.len(),
        zstd::encode_all(&bytes[..], 22).unwrap().len(),
        zstd::bulk::compress(&bytes, 16).unwrap().len()
    );
    let case = mdoc_zk_testcases::vectors::ALL_TEST_CASES
        .iter()
        .find(|case| {
            if case.name.starts_with("fail-") {
                return false;
            }
            let (_, parsed, _) =
                mdoc_zk_circuits::parse_test_data::<4, compile_algebra::CompileNat<4>>(case.data);
            parsed.attrs.len() >= n
                && case.data.doc_type.starts_with("org.iso.18013.5.1")
                && parsed
                    .attrs
                    .iter()
                    .take(n)
                    .all(|a| mdoc_zk_runtime::circuit_supports(&a.cbor_value))
        })
        .expect("positive mdoc fixture for attribute count");
    let (pk, parsed, now) =
        mdoc_zk_circuits::parse_test_data::<4, compile_algebra::CompileNat<4>>(case.data);
    let attrs: Vec<_> = parsed
        .attrs
        .iter()
        .take(n)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();
    let pkx = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pky = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&pk.1.to_bytes_le()).to_str_radix(16)
    );
    let proof = run_mdoc_prover_inner(
        &spec,
        &compressed,
        case.data.mdoc,
        &pkx,
        &pky,
        case.data.transcript,
        &attrs,
        now,
        case.data.doc_type,
        &mut DeterministicRng::new(42),
    )
    .unwrap();
    run_mdoc_verifier_inner(
        &spec,
        &compressed,
        &pkx,
        &pky,
        case.data.transcript,
        &attrs,
        now,
        case.data.doc_type,
        &proof,
    )
    .unwrap();
    println!(
        "TRAVERSAL_PROOF attrs={n} policy={policy} bytes={} verified=true",
        proof.len()
    );
}

fn uleb_len(mut value: usize) -> usize {
    let mut result = 1;
    while value >= 0x80 {
        value >>= 7;
        result += 1;
    }
    result
}

fn zigzag(value: u32) -> usize {
    ((value << 1) ^ ((value as i32 >> 31) as u32)) as usize
}

fn print_lfc2_breakdown(
    field: &CompileFp24Ext6,
    circuit: &compile_eval::Circuit<CompileFp24Ext6>,
    total: usize,
) {
    use std::{collections::HashSet, hash::Hasher};

    let mut metadata = 4 + 32;
    for value in [
        FieldID::None as usize,
        circuit.raw.noutput,
        1,
        circuit.raw.npublic_input,
        circuit.raw.subfield_boundary,
        circuit.raw.ninput,
        circuit.raw.layers.len(),
    ] {
        metadata += uleb_len(value);
    }
    let constants =
        uleb_len(circuit.raw.constants.len()) + circuit.raw.constants.len() * SERIALIZED_SIZE;
    let mut deltas = 0;
    let mut segments = 0;
    let mut tokens = 0;
    let mut layer_local_deltas = 0;
    let mut global_deltas = HashSet::<core_proto::TermDelta>::new();
    let mut singleton_deltas = 0;
    let mut deltas_used_at_most_four_times = 0;
    let mut segment_hashes = HashSet::new();
    let mut segment_count = 0;
    for layer in &circuit.raw.layers {
        metadata += uleb_len(layer.logw()) + uleb_len(layer.nw());
        deltas += uleb_len(layer.deltas().len());
        layer_local_deltas += layer.deltas().len();
        global_deltas.extend(layer.deltas().iter().copied());
        let mut frequencies = vec![0u32; layer.deltas().len()];
        layer.for_each_delta_index(|index| frequencies[index as usize] += 1);
        singleton_deltas += frequencies
            .iter()
            .filter(|&&frequency| frequency == 1)
            .count();
        deltas_used_at_most_four_times += frequencies
            .iter()
            .filter(|&&frequency| frequency <= 4)
            .count();
        for delta in layer.deltas() {
            deltas += uleb_len(zigzag(delta.g));
            deltas += uleb_len(zigzag(delta.h[0]));
            deltas += uleb_len(zigzag(delta.h[1]));
            deltas += uleb_len(delta.k_index as usize);
        }
        segments += uleb_len(layer.delta_segments().len());
        for segment in layer.delta_segments() {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            for &index in segment {
                std::hash::Hash::hash(&layer.deltas()[index as usize], &mut hasher);
            }
            segment_hashes.insert((segment.len(), hasher.finish()));
            segment_count += 1;
            segments += uleb_len(segment.len());
            segments += segment
                .iter()
                .map(|&index| uleb_len(index as usize))
                .sum::<usize>();
        }
        tokens += uleb_len(layer.delta_tokens().len());
        tokens += layer
            .delta_tokens()
            .iter()
            .map(|&token| uleb_len(token as usize))
            .sum::<usize>();
    }
    assert_eq!(metadata + constants + deltas + segments + tokens, total);
    eprintln!(
        "LFC2 breakdown: metadata={metadata}, constants={constants}, deltas={deltas}, segments={segments}, tokens={tokens}"
    );
    eprintln!(
        "LFC2 uniqueness: layer_local_deltas={layer_local_deltas}, global_delta_tuples={}, singleton_deltas={singleton_deltas}, deltas_used_at_most_four_times={deltas_used_at_most_four_times}, layer_local_segments={segment_count}, global_segment_patterns={}",
        global_deltas.len(),
        segment_hashes.len(),
    );

    let mut one_copies = 0;
    let mut direct_copies = 0;
    let mut scalar_linear = 0;
    let mut single_quadratic = 0;
    let mut sums = 0;
    let mut assertion_markers = 0;
    let mut direct_copies_by_layer = Vec::new();
    for layer in &circuit.raw.layers {
        let direct_copies_before = direct_copies;
        let mut gates = Vec::<Vec<(bool, bool, u32, u32)>>::new();
        layer.for_each_term(&circuit.raw.constants, |term| {
            if gates.len() <= term.g as usize {
                gates.resize_with(term.g as usize + 1, Vec::new);
            }
            gates[term.g as usize].push((
                field.is_zero(&term.k),
                term.k == field.one(),
                term.h0,
                term.h1,
            ));
        });
        for gate in gates {
            if gate.len() != 1 {
                sums += 1;
                continue;
            }
            let (is_zero, is_one, h0, h1) = gate[0];
            if is_zero {
                assertion_markers += 1;
            } else if is_one && h0 == 0 && h1 == 0 {
                one_copies += 1;
            } else if is_one && (h0 == 0 || h1 == 0) {
                direct_copies += 1;
            } else if h0 == 0 || h1 == 0 {
                scalar_linear += 1;
            } else {
                single_quadratic += 1;
            }
        }
        direct_copies_by_layer.push(direct_copies - direct_copies_before);
    }
    eprintln!(
        "gate forms: one_copies={one_copies}, direct_copies={direct_copies}, scalar_linear={scalar_linear}, single_quadratic={single_quadratic}, sums={sums}, assertion_markers={assertion_markers}"
    );
    eprintln!(
        "direct copies by layer (input to output): {:?}",
        direct_copies_by_layer.iter().rev().collect::<Vec<_>>()
    );
}

fn compile_and_evaluate<P: MlDsaParams>(example: &[Vec<u8>]) -> CircuitGeometry {
    let instance = ConcreteInstance::<P>::new(&example[1], &example[4], &example[0], &example[2])
        .expect("C++ example must produce a valid Rust witness");
    assert_eq!(instance.mu.as_slice(), example[3]);
    let compile_field = CompileFp24Ext6::new();
    let runtime_field = RuntimeFp24Ext6::new();
    let (circuit, geometry, symbols) = compile_verifier::<P>(&compile_field);
    eprintln!("ML-DSA compile complete: {geometry:?}");
    let writer = core_proto::writer::CircuitWriter::new(&compile_field, FieldID::None);
    let lfc1 = writer.to_bytes_lfc1(&circuit);
    eprintln!("ML-DSA LFC1 serialization complete: {}", lfc1.len());
    let lfc1_compressed = zstd::bulk::compress(&lfc1, 16).unwrap();
    let lfc1_compressed_max = zstd::bulk::compress(&lfc1, 22).unwrap();
    eprintln!("ML-DSA LFC1 compression complete");
    let segmented_circuit = compile_compiler::segment_circuit(&compile_field, &circuit);
    eprintln!("ML-DSA segmentation complete");
    for (index, layer) in segmented_circuit.raw.layers.iter().rev().enumerate() {
        eprintln!(
            "ML-DSA layer {:>2}: wires={:>8}, terms={:>9}, deltas={:>8}, segments={:>6}, tokens={:>8}",
            index + 1,
            layer.nw(),
            layer.num_terms(),
            layer.deltas().len(),
            layer.delta_segments().len(),
            layer.delta_tokens().len(),
        );
    }
    let lfc2 = writer.to_bytes_lfc2(&segmented_circuit);
    print_lfc2_breakdown(&compile_field, &segmented_circuit, lfc2.len());
    let compressed = zstd::bulk::compress(&lfc2, 16).unwrap();
    let compressed_max = zstd::bulk::compress(&lfc2, 22).unwrap();
    eprintln!(
        "ML-DSA geometry: {geometry:?}; LFC1={} bytes; LFC1+zstd16={} bytes; LFC1+zstd22={} bytes; LFC2={} bytes; LFC2+zstd16={} bytes; LFC2+zstd22={} bytes",
        lfc1.len(),
        lfc1_compressed.len(),
        lfc1_compressed_max.len(),
        lfc2.len(),
        compressed.len(),
        compressed_max.len()
    );
    let mut inputs = compile_eval::initial_inputs(&runtime_field);
    instance.push_wires(&runtime_field, &mut inputs);
    compile_eval::eval_circuit_fc(
        &compile_field,
        &runtime_field,
        &segmented_circuit,
        &symbols,
        &inputs,
        FieldID::None,
    )
    .unwrap()
    .assert_all_passed();
    geometry
}

#[test]
#[ignore = "large end-to-end circuit"]
fn full_mldsa44_circuit_accepts_cpp_vector() {
    let source = include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc");
    let example = first_cpp_example(source, "GetMlDsa44Examples()");
    let _ = compile_and_evaluate::<MlDsa44>(&example);
}

#[test]
#[ignore = "large end-to-end circuit"]
fn full_mldsa65_circuit_accepts_cpp_vector() {
    let source = include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc");
    let example = first_cpp_example(source, "GetMlDsa65Examples()");
    let _ = compile_and_evaluate::<MlDsa65>(&example);
}

fn prove_and_verify<P: MlDsaParams>(example: &[Vec<u8>]) {
    use crate::memory::Measurement;
    use circuits_experimental::mldsa::{algebra::RuntimeFp24Subfield, crt::CrtReedSolomonFactory};
    use runtime_ligero::LigeroConfig;
    use runtime_zk::{ZkProver, ZkVerifier};

    let total_start = std::time::Instant::now();
    let instance = ConcreteInstance::<P>::new(&example[1], &example[4], &example[0], &example[2])
        .expect("C++ example must produce a valid Rust witness");
    assert_eq!(instance.mu.as_slice(), example[3]);
    let compile_field = CompileFp24Ext6::new();
    let runtime_field = RuntimeFp24Ext6::new();
    let (compile_circuit, geometry, _) = compile_verifier::<P>(&compile_field);
    let writer = core_proto::writer::CircuitWriter::new(&compile_field, FieldID::None);
    let wire_ordered_circuit = if let Ok(policy) = std::env::var("MLDSA_WIRE_POLICY") {
        assert!(std::env::var_os("MLDSA_LANE_ORDER").is_none());
        assert!(std::env::var_os("MLDSA_TEMPLATE_ROUNDTRIP").is_none());
        morton_analysis::fixed_input_wire_order(&compile_field, &compile_circuit, &policy)
    } else {
        compile_circuit
    };
    let lane_ordered_circuit = if std::env::var_os("MLDSA_LANE_ORDER").is_some() {
        morton_analysis::lane_order(&compile_field, &wire_ordered_circuit)
    } else {
        wire_ordered_circuit
    };
    let benchmark_circuit = if std::env::var_os("MLDSA_TEMPLATE_ROUNDTRIP").is_some() {
        let recovered = morton_analysis::template_roundtrip(&compile_field, &lane_ordered_circuit);
        assert_eq!(
            writer.to_bytes_lfc1(&recovered),
            writer.to_bytes_lfc1(&lane_ordered_circuit)
        );
        eprintln!(
            "Template roundtrip: exact canonical LFC1 and circuit ID; proving decoded circuit"
        );
        recovered
    } else {
        lane_ordered_circuit
    };
    let benchmark_circuit = if let Ok(path) = std::env::var("MLDSA_TRAVERSAL_CIRCUIT") {
        let bytes = std::fs::read(path).unwrap();
        let (candidate, tail) =
            core_proto::reader::CircuitReader::new(&compile_field, FieldID::None)
                .from_bytes_lfc2(&bytes, true)
                .unwrap();
        assert!(tail.is_empty());
        morton_analysis::assert_same_terms(&compile_field, &benchmark_circuit, &candidate);
        candidate
    } else {
        benchmark_circuit
    };
    let lfc1 = writer.to_bytes_lfc1(&benchmark_circuit);
    let lfc1_len = lfc1.len();
    let lfc1_zstd16_len = zstd::bulk::compress(&lfc1, 16).unwrap().len();
    let lfc1_zstd22_len = zstd::bulk::compress(&lfc1, 22).unwrap().len();
    drop(lfc1);
    let segmented_circuit = compile_compiler::segment_circuit(&compile_field, &benchmark_circuit);
    let circuit_bytes = writer.to_bytes_lfc2(&segmented_circuit);
    let lfc2_zstd16_len = zstd::bulk::compress(&circuit_bytes, 16).unwrap().len();
    let lfc2_zstd22_len = zstd::bulk::compress(&circuit_bytes, 22).unwrap().len();
    let id_hex: String = segmented_circuit
        .id
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let layer_deltas: usize = segmented_circuit
        .raw
        .layers
        .iter()
        .map(|l| l.deltas().len())
        .sum();
    let segments: usize = segmented_circuit
        .raw
        .layers
        .iter()
        .map(|l| l.num_segments())
        .sum();
    eprintln!("circuit storage: id={id_hex}, layer_deltas={layer_deltas}, segments={segments}");
    eprintln!(
        "sweep circuit: period={}, geometry={geometry:?}, lfc1={lfc1_len}, lfc1_zstd16={lfc1_zstd16_len}, lfc1_zstd22={lfc1_zstd22_len}, lfc2={}, lfc2_zstd16={lfc2_zstd16_len}, lfc2_zstd22={lfc2_zstd22_len}",
        slice_period(),
        circuit_bytes.len(),
    );
    let (runtime_circuit, remaining) =
        core_proto::reader::CircuitReader::new(&runtime_field, FieldID::None)
            .from_bytes_lfc2(&circuit_bytes, true)
            .unwrap();
    assert!(remaining.is_empty());
    let mut inputs = compile_eval::initial_inputs(&runtime_field);
    instance.push_wires(&runtime_field, &mut inputs);

    let interpolation = CrtReedSolomonFactory;
    let (num_witness, num_constraints) =
        runtime_proto::witness_and_constraint_count(&runtime_circuit);
    let block_enc = runtime_ligero::optimize_geometry(
        num_witness,
        num_constraints,
        4,
        128,
        runtime_field.serialized_size_bytes(),
        RuntimeFp24Subfield.serialized_size_bytes(),
        &interpolation,
    );
    let config = LigeroConfig {
        rateinv: 4,
        nreq: 128,
        block_enc,
    };
    eprintln!(
        "proof setup: geometry={geometry:?}, witnesses={num_witness}, constraints={num_constraints}, block_enc={block_enc}"
    );
    let public_count = runtime_circuit.raw.npublic_input;
    let order = match std::env::var("MLDSA_SUMCHECK_ORDER").as_deref() {
        Err(std::env::VarError::NotPresent) | Ok("hand-major") => {
            runtime_zk::SumcheckOrder::HandMajor
        }
        Ok("round-major") => runtime_zk::SumcheckOrder::RoundMajor,
        value => panic!("invalid MLDSA_SUMCHECK_ORDER: {value:?}"),
    };
    eprintln!("sumcheck order: {order:?}");
    let prover = ZkProver::<3, _>::new(runtime_circuit, config).with_sumcheck_order(order);
    let context = runtime_zk::common::ZkContext {
        f: &runtime_field,
        make_interpolator: &interpolation,
    };
    let subfield = RuntimeFp24Subfield;
    assert_eq!(subfield.serialized_size_bytes(), 3);
    let mut rng = DeterministicRng::new(42);
    let mut prover_transcript = Transcript::new(b"mldsa-rust-benchmark");
    let commit_heap = Measurement::start();
    let commit_start = std::time::Instant::now();
    let (commitment, proof_geometry) = prover.commit(
        &inputs[public_count..],
        &context,
        &mut prover_transcript,
        &mut rng,
        &subfield,
    );
    let commit_time = commit_start.elapsed();
    let commit_peak = commit_heap.finish();
    let prove_heap = Measurement::start();
    let prove_start = std::time::Instant::now();
    let proof = prover
        .prove(
            inputs[..public_count].to_vec(),
            inputs[public_count..].to_vec(),
            &commitment,
            &mut prover_transcript,
            &context,
        )
        .unwrap();
    let prove_time = prove_start.elapsed();
    let prove_peak = prove_heap.finish();
    let proof_bytes = proof
        .write(&proof_geometry, &runtime_field, &subfield)
        .unwrap();

    let verifier = ZkVerifier::new(prover.circuit, config).with_sumcheck_order(order);
    // Exercise the stored proof as well as the stored LFC2 circuit. Serialization
    // and deserialization stay outside the cryptographic timing measurements.
    let verifier_geometry = verifier.geometry(&context);
    assert_eq!(proof_geometry, verifier_geometry);
    let mut proof_slice = proof_bytes.as_slice();
    let decoded_proof = runtime_proto::ZkProof::read(
        &mut proof_slice,
        &verifier_geometry,
        &runtime_field,
        &subfield,
    )
    .unwrap();
    assert!(proof_slice.is_empty());
    assert_eq!(proof, decoded_proof);
    let mut verifier_transcript = Transcript::new(b"mldsa-rust-benchmark");
    let verify_heap = Measurement::start();
    let verify_start = std::time::Instant::now();
    verifier.recv_commitment(&decoded_proof, &mut verifier_transcript, &context);
    verifier
        .verify(
            inputs[..public_count].to_vec(),
            &decoded_proof,
            &mut verifier_transcript,
            &context,
        )
        .unwrap();
    let verify_time = verify_start.elapsed();
    let verify_peak = verify_heap.finish();
    if cfg!(feature = "bench-memory") {
        eprintln!(
            "heap bytes: commit_peak_additional={}, prove_peak_additional={}, prover_total_peak_additional={}, verify_peak_additional={}",
            commit_peak.additional(),
            prove_peak.additional(),
            commit_peak.high.max(prove_peak.high).saturating_sub(commit_peak.baseline),
            verify_peak.additional(),
        );
    }
    eprintln!(
        "sweep proof: period={}, commit={commit_time:?}, prove={prove_time:?}, verify={verify_time:?}, proof={} bytes, total={:?}",
        slice_period(),
        proof_bytes.len(),
        total_start.elapsed()
    );
}

#[test]
#[ignore = "multi-minute proof benchmark"]
fn mldsa44_proof_benchmark() {
    let source = include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc");
    prove_and_verify::<MlDsa44>(&first_cpp_example(source, "GetMlDsa44Examples()"));
}

#[test]
#[ignore = "multi-minute proof benchmark"]
fn mldsa65_proof_benchmark() {
    let source = include_str!("../../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc");
    prove_and_verify::<MlDsa65>(&first_cpp_example(source, "GetMlDsa65Examples()"));
}
