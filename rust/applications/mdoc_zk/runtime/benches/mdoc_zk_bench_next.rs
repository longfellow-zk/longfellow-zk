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

//! Complete v8 flow, including circuit loading, native preparation, commitments,
//! serialization and cleanup. Longfellow v2 uses the checked Polygero parameter family.
use std::time::Instant;

#[path = "../../../../benches/support/memory.rs"]
mod memory;

use longfellow_zk::{
    compile::algebra::CompileNat,
    core::algebra::Nat,
    mdoc::{
        circuits::parse_test_data,
        v2::{self as runtime, req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner},
    },
    runtime::random::DeterministicRng,
};
fn main() {
    let data = &longfellow_zk::mdoc::testcases::vectors::TEST_DATA;
    let (issuer_pk, parsed, now) = parse_test_data::<4, CompileNat<4>>(data);
    let attrs: Vec<_> = parsed
        .attrs
        .iter()
        .take(2)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();
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
        "Longfellow v2 / NEXT v{}; parameters checked in the ideal-binding one-level FS model.",
        longfellow_zk::mdoc::circuits::NEXT_VERSION
    );
    eprintln!(
        "Offline circuit preparation: {:.3} ms",
        offline.elapsed().as_secs_f64() * 1000.0
    );
    let geometry = report_profiles(&circuits, &spec);
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
    eprintln!(
        "Longfellow v2 (circuit v8) end to end: prover={:.3} ms, verifier={:.3} ms, proof={} bytes",
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
    use longfellow_zk::runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        zk_v2::ZkContext,
    };
    let binary = Gf2_128Field::new();
    let subfield = longfellow_zk::runtime::algebra::subfield_v1::BinarySubfield::new(
        &longfellow_zk::core::algebra::proto::GF2_16_BASIS_V1,
    );
    let binary_domain = BinaryInterpolatorFactory::new(&binary, &subfield);
    let prime = P256Field::new();
    let extension = Fp2Field::new(&prime);
    let prime_domain = QuadraticExtensionFftInterpolatorFactory::new(
        &prime,
        &extension,
        extension.omega(),
        extension.omega_order(),
    );
    let (signature, hash) = runtime::decompress_circuits(circuits, &prime, &binary, false).unwrap();
    let hash_context = ZkContext {
        f: &binary,
        domain: &binary_domain,
    };
    let signature_context = ZkContext {
        f: &prime,
        domain: &prime_domain,
    };
    let (hash_config, signature_config) = spec.configs();
    eprintln!("  Selected hash profile: {hash_config:?}");
    eprintln!("  Selected signature profile: {signature_config:?}");
    let hash_verifier =
        longfellow_zk::runtime::zk_v2::ZkVerifier::new_full_field(hash, hash_config, &hash_context)
            .unwrap();
    let signature_verifier = longfellow_zk::runtime::zk_v2::ZkVerifier::new(
        signature,
        signature_config,
        &signature_context,
    )
    .unwrap();
    runtime::proto::MdocProofGeometry {
        geom_hash: hash_verifier.geometry(),
        geom_sig: signature_verifier.geometry(),
    }
}

/// Measure actual serialized component proofs, excluding the six shared MACs.
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
    let hash_polygero = proof
        .proof_hash
        .com_proof
        .write(&geometry.geom_hash.com_geom, &binary)
        .unwrap();
    let hash_sumcheck = proof
        .proof_hash
        .sumcheck_proof
        .write(&geometry.geom_hash.sc_geom, &binary)
        .unwrap();
    assert_eq!(
        hash.len(),
        4 + 32 + hash_sumcheck.len() + hash_polygero.len()
    );
    assert_eq!(bytes.len(), 96 + hash.len() + signature.len());
    eprintln!(
        "  SHA/hash circuit: {} bytes (Polygero={}, sumcheck={}, version+commitment=36)",
        hash.len(),
        hash_polygero.len(),
        hash_sumcheck.len()
    );
    eprintln!(
        "  Signature circuit: {} bytes; shared MACs: 96 bytes",
        signature.len()
    );
    eprintln!("  Proof SHA256: {:x}", Sha256::digest(bytes));
}
