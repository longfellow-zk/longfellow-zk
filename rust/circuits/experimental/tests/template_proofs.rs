// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! End-to-end ordinary LFC2 benchmarks, with fixture construction and circuit compilation
//! excluded. Run timing without bench-memory, heap runs with it, in isolation.
#[path = "support/memory.rs"]
mod memory;
#[path = "all/mldsa_test_vectors.rs"]
mod vectors;

use core_proto::{FieldID, SerializableField};
use runtime_random::{DeterministicRng, Transcript};
use std::time::Instant;

fn load<F: SerializableField>(
    f: &F,
    field: FieldID,
    path: &str,
) -> core_proto::circuit::Circuit<F> {
    let bytes = std::fs::read(path).unwrap();
    let reader = core_proto::reader::CircuitReader::new(f, field);
    let reader = if let Ok(limit) = std::env::var("ORDER_TOTAL_TERM_LIMIT") {
        reader.with_total_term_limit(limit.parse().unwrap())
    } else {
        reader
    };
    let (c, tail) = reader.from_bytes(&bytes, true).unwrap();
    assert!(tail.is_empty());
    c
}

fn rss() -> String {
    std::fs::read_to_string("/proc/self/status")
        .unwrap()
        .lines()
        .filter(|s| s.starts_with("VmRSS:") || s.starts_with("VmHWM:"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn mldsa<P: circuits_experimental::mldsa::params::MlDsaParams>(source: &str, marker: &str) {
    use circuits_experimental::mldsa::{
        algebra::{RuntimeFp24Ext6, RuntimeFp24Subfield},
        crt::CrtReedSolomonFactory,
        verifier::ConcreteInstance,
    };
    use runtime_algebra::Subfield;
    use runtime_zk::{common::ZkContext, ZkProver, ZkVerifier};
    println!(
        "GRID_CONFIG period={} first={} bits={}",
        circuits_experimental::mldsa::shake::slice_period(),
        circuits_experimental::mldsa::shake::first_round_slice() as u8,
        circuits_experimental::mldsa::shake::plucker_bits()
    );
    assert!((1..=6).contains(&circuits_experimental::mldsa::shake::slice_period()));
    let order = match std::env::var("ORDER_SUMCHECK").as_deref().unwrap_or("hand") {
        "hand" => runtime_sumcheck::SumcheckOrder::HandMajor,
        "round" => runtime_sumcheck::SumcheckOrder::RoundMajor,
        _ => panic!("ORDER_SUMCHECK must be hand or round"),
    };
    let f = RuntimeFp24Ext6::new();
    let sf = RuntimeFp24Subfield;
    let example = vectors::first_cpp_example(source, marker);
    let instance =
        ConcreteInstance::<P>::new(&example[1], &example[4], &example[0], &example[2]).unwrap();
    let mut inputs = compile_eval::initial_inputs(&f);
    instance.push_wires(&f, &mut inputs);
    assert!(inputs.iter().all(|value| sf.contains(value)));
    drop(instance);
    let path = std::env::var("ORDER_PROOF_CIRCUIT").unwrap();
    let repeats: usize = std::env::var("ORDER_REPEATS")
        .unwrap_or_else(|_| "3".into())
        .parse()
        .unwrap();
    for repeat in 0..repeats {
        let start = Instant::now();
        let c = load(&f, FieldID::None, &path);
        let load_ms = start.elapsed().as_secs_f64() * 1000.;
        assert_eq!(core_proto::circuit::compute_id(&f, &c.raw), c.id);
        assert_eq!(inputs.len(), c.raw.ninput);
        assert_eq!(c.raw.subfield_boundary, c.raw.ninput);
        let interpolation = CrtReedSolomonFactory;
        let (nw, nc) = runtime_proto::witness_and_constraint_count(&c);
        let block_enc = runtime_ligero::optimize_geometry(
            nw,
            nc,
            4,
            128,
            f.serialized_size_bytes(),
            sf.serialized_size_bytes(),
            &interpolation,
        );
        let config = runtime_ligero::LigeroConfig {
            rateinv: 4,
            nreq: 128,
            block_enc,
        };
        let public = c.raw.npublic_input;
        let prover = ZkProver::<3, _>::new(c, config).with_sumcheck_order(order);
        let ctx = ZkContext {
            f: &f,
            make_interpolator: &interpolation,
        };
        let mut rng = DeterministicRng::new(42);
        let mut transcript = Transcript::new(b"layer-template-benchmark");
        let before = rss();
        let commit_heap = memory::Measurement::start();
        let start = Instant::now();
        let (commitment, geometry) =
            prover.commit(&inputs[public..], &ctx, &mut transcript, &mut rng, &sf);
        let commit_ms = start.elapsed().as_secs_f64() * 1000.;
        let commit_heap = commit_heap.finish();
        let prove_heap = memory::Measurement::start();
        let start = Instant::now();
        let proof = prover
            .prove(
                inputs[..public].to_vec(),
                inputs[public..].to_vec(),
                &commitment,
                &mut transcript,
                &ctx,
            )
            .unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.;
        let prove_heap = prove_heap.finish();
        let bytes = proof.write(&geometry, &f, &sf).unwrap();
        if let Ok(path) = std::env::var("ORDER_SAVE_PROOF") {
            std::fs::write(path, &bytes).unwrap();
        }
        if let Ok(path) = std::env::var("ORDER_EXPECT_PROOF") {
            assert_eq!(bytes, std::fs::read(path).unwrap());
        }
        drop(commitment);
        drop(proof);
        let verifier = ZkVerifier::new(prover.circuit, config).with_sumcheck_order(order);
        let mut slice = bytes.as_slice();
        let proof = runtime_proto::ZkProof::read(&mut slice, &geometry, &f, &sf).unwrap();
        assert!(slice.is_empty());
        let mut transcript = Transcript::new(b"layer-template-benchmark");
        let verify_heap = memory::Measurement::start();
        let start = Instant::now();
        verifier.recv_commitment(&proof, &mut transcript, &ctx);
        verifier
            .verify(inputs[..public].to_vec(), &proof, &mut transcript, &ctx)
            .unwrap();
        let verify_ms = start.elapsed().as_secs_f64() * 1000.;
        let verify_heap = verify_heap.finish();
        println!("ORDER_PROOF marker={marker} repeat={repeat} load_ms={load_ms:.3} commit_ms={commit_ms:.3} prove_ms={prove_ms:.3} total_prover_ms={:.3} verify_ms={verify_ms:.3} proof={} witnesses={nw} constraints={nc} block_enc={block_enc} commit_heap={} prove_heap={} verify_heap={} commit_extra={} prove_extra={} verify_extra={} before={before} after={}",
            commit_ms + prove_ms, bytes.len(), commit_heap.high, prove_heap.high, verify_heap.high,
            commit_heap.additional(), prove_heap.additional(), verify_heap.additional(), rss());
    }
}

#[test]
#[ignore = "full saved-circuit MLDSA44 benchmark"]
fn mldsa44_template_proof() {
    mldsa::<circuits_experimental::mldsa::params::MlDsa44>(
        include_str!("../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc"),
        "GetMlDsa44Examples()",
    );
}

#[test]
#[ignore = "full saved-circuit MLDSA65 benchmark"]
fn mldsa65_template_proof() {
    mldsa::<circuits_experimental::mldsa::params::MlDsa65>(
        include_str!("../../../../lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc"),
        "GetMlDsa65Examples()",
    );
}

#[test]
#[ignore = "full current mdoc flow on supplied saved circuit pair"]
fn mdoc_template_proof() {
    use core_algebra::Nat;
    use mdoc_zk_runtime::{req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner};
    let n: usize = std::env::var("ORDER_ATTRS")
        .unwrap_or_else(|_| "2".into())
        .parse()
        .unwrap();
    assert!((1..=4).contains(&n));
    let mut spec = mdoc_zk_runtime::CURRENT_ZK_SPECS[n - 1];
    let compressed = if let Ok(path) = std::env::var("ORDER_MDOC_ARCHIVE") {
        // Benchmark container: trusted spec ID followed by the zstd LFA2 archive.
        // Preparing/compressing the archive must not pollute measured peak RSS.
        let bytes = std::fs::read(path).unwrap();
        spec.combined_hash.copy_from_slice(&bytes[..32]);
        bytes[32..].to_vec()
    } else {
        let sig_path = std::env::var("ORDER_SIG").unwrap();
        let hash_path = std::env::var("ORDER_HASH").unwrap();
        let sig = load(
            &runtime_algebra::p256::P256Field::new(),
            FieldID::P256,
            &sig_path,
        );
        let hash = load(
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            FieldID::Gf2_128,
            &hash_path,
        );
        let mut builder = core_proto::archive::CircuitArchiveBuilder::new();
        builder.set_circuit_version(mdoc_zk_circuits::CURRENT_VERSION as u32);
        builder.add_entry("sig", sig.id, std::fs::read(&sig_path).unwrap());
        builder.add_entry("hash", hash.id, std::fs::read(&hash_path).unwrap());
        drop(sig);
        drop(hash);
        let archive = builder.build();
        spec.combined_hash = archive.combined_id;
        let raw = archive.to_bytes();
        drop(archive);
        let compressed = zstd::encode_all(&raw[..], 16).unwrap();
        println!(
            "ORDER_MDOC_ARCHIVE attrs={n} raw={} z16={} z22={}",
            raw.len(),
            compressed.len(),
            zstd::encode_all(&raw[..], 22).unwrap().len()
        );
        drop(raw);
        compressed
    };
    if let Ok(path) = std::env::var("ORDER_SAVE_ARCHIVE") {
        let mut bytes = spec.combined_hash.to_vec();
        bytes.extend(&compressed);
        std::fs::write(path, bytes).unwrap();
        return;
    }
    let case = &mdoc_zk_testcases::vectors::TEST_DATA;
    let (pk, parsed, now) =
        mdoc_zk_circuits::parse_test_data::<4, compile_algebra::CompileNat<4>>(case);
    let attrs: Vec<_> = parsed
        .attrs
        .iter()
        .take(n)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();
    assert_eq!(attrs.len(), n);
    let pkx = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pky = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&pk.1.to_bytes_le()).to_str_radix(16)
    );
    let repeats: usize = std::env::var("ORDER_REPEATS")
        .unwrap_or_else(|_| "3".into())
        .parse()
        .unwrap();
    for repeat in 0..repeats {
        let before = rss();
        let heap = memory::Measurement::start();
        let start = Instant::now();
        let proof = run_mdoc_prover_inner(
            &spec,
            &compressed,
            case.mdoc,
            &pkx,
            &pky,
            case.transcript,
            &attrs,
            now,
            case.doc_type,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.;
        let prove_heap = heap.finish();
        if let Ok(path) = std::env::var("ORDER_SAVE_PROOF") {
            std::fs::write(path, &proof).unwrap();
        }
        if let Ok(path) = std::env::var("ORDER_EXPECT_PROOF") {
            assert_eq!(proof, std::fs::read(path).unwrap());
        }
        let heap = memory::Measurement::start();
        let start = Instant::now();
        run_mdoc_verifier_inner(
            &spec,
            &compressed,
            &pkx,
            &pky,
            case.transcript,
            &attrs,
            now,
            case.doc_type,
            &proof,
        )
        .unwrap();
        let verify_ms = start.elapsed().as_secs_f64() * 1000.;
        let verify_heap = heap.finish();
        println!("ORDER_MDOC_PROOF attrs={n} repeat={repeat} prove_ms={prove_ms:.3} verify_ms={verify_ms:.3} proof={} prove_heap={} verify_heap={} prove_extra={} verify_extra={} before={before} after={}", proof.len(), prove_heap.high, verify_heap.high, prove_heap.additional(), verify_heap.additional(), rss());
    }
}
