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

//! Longfellow v2 / NEXT circuit end-to-end benchmark.

//! Complete NEXT flow, including circuit loading, prime-field preparation, commitments,
//! serialization and cleanup. Longfellow v2 uses the checked Polygero parameter family.
use std::time::Instant;

#[path = "../../../../benches/support/memory.rs"]
mod memory;

use longfellow_zk::{
    compile::algebra::CompileNat,
    core::algebra::Nat,
    mdoc::{
        circuits::parse_test_data,
        v2 as runtime,
        v2::{req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner},
    },
    runtime::random::DeterministicRng,
};
fn main() {
    let attributes = std::env::var("MDOC_BENCH_ATTRIBUTES")
        .unwrap_or_else(|_| "2".into())
        .parse::<usize>()
        .unwrap();
    let samples = std::env::var("MDOC_BENCH_SAMPLES")
        .unwrap_or_else(|_| "8".into())
        .parse::<usize>()
        .unwrap();
    assert!((1..=4).contains(&attributes));
    assert!(
        samples >= 2,
        "one warmup and at least one measured sample required"
    );
    let data = &longfellow_zk::mdoc::testcases::vectors::TEST_DATA;
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(data);
    let attrs: Vec<_> = parsed
        .attrs
        .iter()
        .cycle()
        .take(attributes)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();
    assert_eq!(attrs.len(), attributes);
    let pkx = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16)
    );
    let pky = format!(
        "0x{}",
        num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16)
    );
    let offline = Instant::now();
    let (spec, circuits) = prepare_circuits(attrs.len());
    eprintln!(
        "Longfellow v2 / NEXT v{}; parameters checked in the ideal-oracle extractor model.",
        longfellow_zk::mdoc::circuits::NEXT_VERSION
    );
    eprintln!(
        "Offline circuit preparation: {:.3} ms",
        offline.elapsed().as_secs_f64() * 1000.0
    );
    let geometry = report_profiles(&circuits, &spec);
    let mut prover_times = Vec::new();
    let mut verifier_times = Vec::new();
    println!("attributes,sample,prover_ms,verifier_ms,proof_bytes,prover_heap,verifier_heap");
    for sample in 0..samples {
        memory::reset_peak();
        let prover_baseline = memory::get_current_allocated();
        let prover_start = Instant::now();
        let proof = run_mdoc_prover_inner(
            &spec,
            &circuits,
            data.mdoc,
            &pkx,
            &pky,
            data.transcript,
            &attrs,
            now,
            "org.iso.18013.5.1.mDL",
            &mut DeterministicRng::new(42),
        )
        .unwrap();
        let prover = prover_start.elapsed();
        let prover_peak = memory::get_peak_allocated().saturating_sub(prover_baseline);
        memory::reset_peak();
        let verifier_baseline = memory::get_current_allocated();
        let verifier_start = Instant::now();
        run_mdoc_verifier_inner(
            &spec,
            &circuits,
            &pkx,
            &pky,
            data.transcript,
            &attrs,
            now,
            "org.iso.18013.5.1.mDL",
            &proof,
        )
        .unwrap();
        let verifier = verifier_start.elapsed();
        let verifier_peak = memory::get_peak_allocated().saturating_sub(verifier_baseline);
        let pm = prover.as_secs_f64() * 1000.0;
        let vm = verifier.as_secs_f64() * 1000.0;
        println!(
            "{attributes},{sample},{pm:.6},{vm:.6},{},{prover_peak},{verifier_peak}",
            proof.len()
        );
        if sample > 0 {
            prover_times.push(pm);
            verifier_times.push(vm);
        }
        if sample + 1 != samples {
            continue;
        }
        eprintln!(
            "Longfellow v2 end to end: prover={:.3} ms, verifier={:.3} ms, proof={} bytes",
            prover.as_secs_f64() * 1000.0,
            verifier.as_secs_f64() * 1000.0,
            proof.len()
        );
        report_proof_sizes(&proof, &geometry);
        if cfg!(feature = "bench-memory") {
            eprintln!(
            "  End-to-end additional peak heap: prover={prover_peak}, verifier={verifier_peak} bytes"
        );
        }
        let mut bad = proof.clone();
        let last = bad.len() - 1;
        bad[last] ^= 1;
        assert!(run_mdoc_verifier_inner(
            &spec,
            &circuits,
            &pkx,
            &pky,
            data.transcript,
            &attrs,
            now,
            "org.iso.18013.5.1.mDL",
            &bad
        )
        .is_err());
    }
    prover_times.sort_by(f64::total_cmp);
    verifier_times.sort_by(f64::total_cmp);
    let median = |values: &[f64]| (values[(values.len() - 1) / 2] + values[values.len() / 2]) / 2.0;
    eprintln!(
        "Median after warmup: prover={:.6} ms verifier={:.6} ms",
        median(&prover_times),
        median(&verifier_times)
    );
}

/// Prepare the spec/archive pair before online timing; decoded archive storage stays here.
fn prepare_circuits(num_attributes: usize) -> (runtime::ZkSpecStruct, Vec<u8>) {
    let provided = if let Some(path) = std::env::var_os("MDOC_BENCH_ARCHIVE") {
        longfellow_zk::mdoc::development_provider::read_next(std::fs::File::open(path).unwrap())
            .unwrap()
    } else {
        longfellow_zk::mdoc::development_provider::compile_next(num_attributes).unwrap()
    };
    assert_eq!(provided.spec().num_attributes, num_attributes);
    if let Some(path) = std::env::var_os("MDOC_BENCH_SAVE_ARCHIVE") {
        longfellow_zk::mdoc::development_provider::write_next(
            std::fs::File::create(path).unwrap(),
            &provided,
        )
        .unwrap();
    }
    provided.into_parts()
}

/// Report the selected public profiles and derive sizes outside timed operations.
fn report_profiles(
    circuits: &[u8],
    spec: &runtime::ZkSpecStruct,
) -> runtime::proto::MdocProofGeometry {
    use longfellow_zk::runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field};
    let binary = Gf2_128Field::new();
    let prime = P256Field::new();
    let baseline = memory::get_current_allocated();
    let (signature, hash) = runtime::decompress_circuits(circuits, &prime, &binary, false).unwrap();
    if cfg!(feature = "bench-memory") {
        eprintln!(
            "Decoded circuit heap: {} bytes",
            memory::get_current_allocated().saturating_sub(baseline)
        );
    }
    eprintln!(
        "Circuit archive: compressed={} raw={} bytes",
        circuits.len(),
        zstd::decode_all(circuits).unwrap().len()
    );
    fn report<F: longfellow_zk::core::algebra::SerializableField>(
        name: &str,
        c: &longfellow_zk::core::proto::v2::Circuit<F>,
    ) {
        eprintln!(
            "{name} circuit: inputs={} outputs={} layers={} rounds={} wires={} terms={}",
            c.raw.ninput,
            c.raw.noutput,
            c.raw.layers.len(),
            c.raw.layers.iter().map(|l| l.logw()).sum::<usize>(),
            c.raw.layers.iter().map(|l| l.nw()).sum::<usize>() - c.raw.ninput + c.raw.noutput,
            c.raw.layers.iter().map(|l| l.num_terms()).sum::<usize>()
        );
    }
    report("Hash", &hash);
    report("Signature", &signature);
    let (hash_config, signature_config) = spec.configs();
    eprintln!("  Selected hash profile: {hash_config:?}");
    eprintln!("  Selected signature profile: {signature_config:?}");
    runtime::proof_geometry(spec, &signature, &hash).unwrap()
}

/// Measure actual serialized proof bodies and adapter messages.
fn report_proof_sizes(bytes: &[u8], geometry: &runtime::proto::MdocProofGeometry) {
    use longfellow_zk::runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field};
    use sha2::{Digest, Sha256};
    let binary = Gf2_128Field::new();
    let prime = P256Field::new();
    let (remaining, proof) =
        runtime::proto::MdocProof::read(bytes, geometry, &binary, &prime).unwrap();
    assert!(remaining.is_empty());
    let hash = proof
        .proof_hash
        .write(&geometry.geom_hash, &binary)
        .unwrap();
    let signature = proof.proof_sig.write(&geometry.geom_sig, &prime).unwrap();
    let polygero = &proof.polygero;
    let (nonces, frontier) = polygero.authentication_bytes();
    let hash_payload = polygero.bodies().0.payload_bytes(&binary);
    let signature_payload = polygero.bodies().1 .0.payload_bytes(&prime);
    let shared_bytes = 36 + hash_payload + signature_payload + nonces + frontier;
    assert_eq!(
        bytes.len(),
        32 + proof.masked.len() + 36 + 96 + hash.len() + signature.len() + shared_bytes + 32
    );
    eprintln!(
        "  SHA/hash reduction: {} bytes; signature reduction: {} bytes",
        hash.len(),
        signature.len()
    );
    eprintln!("  Shared Polygero: {shared_bytes} bytes (hash={hash_payload}, signature={signature_payload}, nonces={nonces}, frontier={frontier}, context+version=36)");
    eprintln!("  Witness fingerprints: 96 bytes (binary=32, signature=64)");
    eprintln!(
        "  Adapter: {} bytes; version+commitment: 36 bytes",
        32 + proof.masked.len()
    );
    eprintln!("  Proof SHA256: {:x}", Sha256::digest(bytes));
}
