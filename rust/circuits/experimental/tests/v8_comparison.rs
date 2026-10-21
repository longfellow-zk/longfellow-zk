// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Identical benchmark source for current single-hand and the old hand-major tree.
//! Select the implementation by the source tree, never by changing circuit storage.
//! Run with --ignored --nocapture --test-threads=1; bench-memory is a separate run.
#[path = "support/memory.rs"]
mod memory;

use core_algebra::Nat;
use core_proto::circuit::Circuit;
use runtime_algebra::{ElementOf, InterpolatorFactory, Subfield, ZkField};
use runtime_random::{DeterministicRng, RandomEngine, Transcript};
use runtime_zk_ng::{common::ZkContext, ZkProver, ZkVerifier};
use std::time::Instant;

fn variable(name: &str, default: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| default.into())
}

fn identifier(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[allow(clippy::too_many_arguments)]
fn component<const W: usize, F, IF, SF>(
    name: &str,
    circuit: Circuit<F>,
    public: &[ElementOf<F>],
    witness: &[ElementOf<F>],
    config: runtime_ligero::LigeroConfig,
    context: &ZkContext<'_, W, F, IF>,
    subfield: &SF,
    repeat: usize,
    warmup: bool,
) where
    F: ZkField<W>,
    IF: InterpolatorFactory<W, F>,
    SF: Subfield<E = ElementOf<F>>,
{
    let f = context.f;
    let id = identifier(&circuit.id);
    let prover = ZkProver::new(circuit, config);
    let mut rng = DeterministicRng::new(42);
    let mut pt = Transcript::new(b"v8-protocol-comparison-component");
    let (geometry, bytes, sumcheck_bytes, commit_ms, prove_ms, commit_heap, prove_heap) = {
        let commit_heap = memory::Measurement::start();
        let start = Instant::now();
        let (commitment, geometry) = prover.commit(witness, context, &mut pt, &mut rng, subfield);
        let commit_ms = start.elapsed().as_secs_f64() * 1000.;
        let commit_heap = commit_heap.finish();
        let prove_heap = memory::Measurement::start();
        let start = Instant::now();
        let proof = prover
            .prove(
                public.to_vec(),
                witness.to_vec(),
                &commitment,
                &mut pt,
                context,
            )
            .unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.;
        let prove_heap = prove_heap.finish();
        let bytes = proof.write(&geometry, f, subfield).unwrap();
        let sumcheck_bytes = proof
            .sumcheck_proof
            .write(&geometry.sc_geom, f)
            .unwrap()
            .len();
        (
            geometry,
            bytes,
            sumcheck_bytes,
            commit_ms,
            prove_ms,
            commit_heap,
            prove_heap,
        )
    };
    let verifier = ZkVerifier::new(prover.circuit, config);
    assert_eq!(geometry, verifier.geometry(context));
    let mut remaining = bytes.as_slice();
    let decoded =
        runtime_proto::zk_ng::ZkProof::read(&mut remaining, &geometry, f, subfield).unwrap();
    assert!(remaining.is_empty());
    let mut vt = Transcript::new(b"v8-protocol-comparison-component");
    let verify_heap = memory::Measurement::start();
    let start = Instant::now();
    verifier.recv_commitment(&decoded, &mut vt, context);
    verifier
        .verify(public.to_vec(), &decoded, &mut vt, context)
        .unwrap();
    let verify_ms = start.elapsed().as_secs_f64() * 1000.;
    let verify_heap = verify_heap.finish();
    assert_eq!(pt.bytes(32), vt.bytes(32));
    println!("V8_COMPONENT label={} geometry={} attrs={} component={name} repeat={repeat} warmup={warmup} memory={} circuit={id} commit_ms={commit_ms:.6} prove_ms={prove_ms:.6} total_prover_ms={:.6} verify_ms={verify_ms:.6} proof_bytes={} sumcheck_bytes={sumcheck_bytes} block_enc={} nrow={} commit_extra={} prove_extra={} prover_total_extra={} verify_extra={}",
        variable("V8_LABEL","current"), variable("V8_GEOMETRY","native"), variable("V8_ATTRS","2"),
        cfg!(feature="bench-memory"), commit_ms + prove_ms, bytes.len(), config.block_enc, geometry.com_geom.nrow,
        commit_heap.additional(), prove_heap.additional(),
        commit_heap.high.max(prove_heap.high).saturating_sub(commit_heap.baseline), verify_heap.additional());
}

#[test]
#[ignore = "controlled v8 old/new performance comparison"]
fn v8_comparison() {
    use mdoc_zk_runtime::{req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner};
    use runtime_algebra::SupportsFFT;
    let n: usize = variable("V8_ATTRS", "2").parse().unwrap();
    assert!((1..=4).contains(&n));
    if let Ok(path) = std::env::var("V8_PREPARE") {
        let provided = mdoc_zk_runtime::provider::materialize(8, n).unwrap();
        let mut bytes = provided.spec.combined_hash.to_vec();
        bytes.extend(provided.compressed);
        std::fs::write(path, bytes).unwrap();
        return;
    }
    let mut spec = mdoc_zk_runtime::CURRENT_ZK_SPECS[n - 1];
    assert_eq!(spec.version, 8);
    match variable("V8_GEOMETRY", "native").as_str() {
        "native" => {}
        "old" => {
            spec.ligero_sig.block_enc = 4445;
            spec.ligero_hash.block_enc = if n == 1 { 5255 } else { 5246 };
        }
        value => panic!("invalid V8_GEOMETRY {value}"),
    }
    let saved =
        std::fs::read(std::env::var("V8_ARCHIVE").expect("set V8_ARCHIVE to a prepared archive"))
            .unwrap();
    assert_eq!(&saved[..32], &spec.combined_hash);
    let compressed = &saved[32..];
    let case = &mdoc_zk_testcases::vectors::TEST_DATA;
    let (pk, parsed_compile, now) =
        mdoc_zk_circuits::parse_test_data::<4, compile_algebra::CompileNat<4>>(case);
    let attrs: Vec<_> = parsed_compile
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
    let p256 = runtime_algebra::p256::P256Field::new();
    let gf2 = runtime_algebra::gf2_128::Gf2_128Field::new();
    let issuer_pk = (
        mdoc_zk_runtime::parse_pk_coordinate(&pkx, &p256).unwrap(),
        mdoc_zk_runtime::parse_pk_coordinate(&pky, &p256).unwrap(),
    );
    let parsed: mdoc_zk_circuits::cbor::mdoc::ParsedMdoc<runtime_algebra::RuntimeNat<4>> =
        mdoc_zk_circuits::cbor::mdoc::parse_mdoc(case.mdoc, case.transcript, case.doc_type)
            .unwrap();
    let mac_ap = mdoc_zk_runtime::generate_mac_ap(&mut DeterministicRng::new(42));
    let av = 42u128;
    let macs = mdoc_zk_runtime::push_macs(
        &gf2,
        8,
        &parsed.issuer_sig_digest,
        &parsed.device_pk,
        av,
        &mac_ap,
    );
    let witness_hash =
        mdoc_zk_runtime::push_witness_hash(8, &gf2, &attrs, &parsed, &mac_ap).unwrap();
    let witness_sig = mdoc_zk_runtime::push_witness_sig(
        8,
        &p256,
        &runtime_algebra::Q256Field::new(),
        &runtime_algebra::secp256r1::Secp256r1::new(&p256),
        &issuer_pk,
        &parsed,
        &mac_ap,
    )
    .unwrap();
    let hash_public = mdoc_zk_runtime::push_input_hash(
        8,
        &gf2,
        &attrs,
        now.as_bytes(),
        &macs,
        av,
        false,
        case.doc_type.as_bytes(),
    );
    let sig_public =
        mdoc_zk_runtime::push_input_sig(8, &p256, &issuer_pk, &parsed.device_sig_digest, &macs, av);
    let sf_hash =
        runtime_algebra::subfield::BinarySubfield::new(&core_algebra::proto::GF2_16_BASIS_V1);
    let hash_interpolation =
        runtime_algebra::lch14_reed_solomon::Lch14InterpolatorFactory::new(&gf2, &sf_hash);
    let p256_2 = runtime_algebra::fp2::Fp2Field::new(&p256);
    let sig_interpolation = runtime_algebra::reed_solomon::FftInterpolatorFactory::new(
        &p256,
        &p256_2,
        p256_2.omega(),
        p256_2.omega_order(),
    );
    let sf_sig = runtime_algebra::p256::P256Subfield::new(&p256);
    let repeats: usize = variable("V8_REPEATS", "5").parse().unwrap();
    let warmups: usize = variable("V8_WARMUPS", "1").parse().unwrap();
    let selected = variable("V8_COMPONENTS", "all");
    assert!(["all", "hash", "sig", "flow"].contains(&selected.as_str()));
    for repeat in 0..warmups + repeats {
        let warmup = repeat < warmups;
        if selected == "all" || selected == "hash" {
            let (_, hash) = mdoc_zk_runtime::decompress_circuits(compressed, &p256, &gf2).unwrap();
            component(
                "hash",
                hash,
                &hash_public,
                &witness_hash,
                spec.ligero_hash,
                &ZkContext {
                    f: &gf2,
                    make_interpolator: &hash_interpolation,
                },
                &sf_hash,
                repeat,
                warmup,
            );
        }
        if selected == "all" || selected == "sig" {
            let (sig, _) = mdoc_zk_runtime::decompress_circuits(compressed, &p256, &gf2).unwrap();
            component(
                "sig",
                sig,
                &sig_public,
                &witness_sig,
                spec.ligero_sig,
                &ZkContext {
                    f: &p256,
                    make_interpolator: &sig_interpolation,
                },
                &sf_sig,
                repeat,
                warmup,
            );
        }
        if selected == "all" || selected == "flow" {
            let prove_heap = memory::Measurement::start();
            let start = Instant::now();
            let proof = run_mdoc_prover_inner(
                &spec,
                compressed,
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
            let prove_heap = prove_heap.finish();
            let verify_heap = memory::Measurement::start();
            let start = Instant::now();
            run_mdoc_verifier_inner(
                &spec,
                compressed,
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
            let verify_heap = verify_heap.finish();
            println!("V8_FLOW label={} geometry={} attrs={n} repeat={repeat} warmup={warmup} memory={} prove_ms={prove_ms:.6} verify_ms={verify_ms:.6} proof_bytes={} prove_extra={} verify_extra={}",
                variable("V8_LABEL","current"),variable("V8_GEOMETRY","native"),cfg!(feature="bench-memory"),
                proof.len(),prove_heap.additional(),verify_heap.additional());
        }
    }
}
