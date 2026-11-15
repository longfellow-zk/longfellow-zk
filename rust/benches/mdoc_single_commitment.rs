// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Scalar mdoc with a single binary-field commitment. Matches the ordinary
//! NEXT benchmark's statement, archive and fixture environment variables.
use std::{fs::File, time::Instant};

use longfellow_zk::{
    mdoc::{
        cbor::{
            mdoc::parse_mdoc,
            test_utils::{parse_test_data, with_mso_size},
        },
        development_provider::{compile_parser_free_next, read_next, write_next},
        testcases::TEST_DATA,
        v2::{decompress_circuits, req_attr, single_commitment},
    },
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, RuntimeNat},
        random::DeterministicRng,
    },
};
mod support;
use support::memory;

fn main() {
    let encoding = match std::env::var("MDOC_BENCH_SIGNATURE_ENCODING").as_deref() {
        Ok("affine-ers") => single_commitment::SignatureEncoding::AffineErs,
        Ok("canonical") => single_commitment::SignatureEncoding::Canonical,
        Err(_) => single_commitment::SignatureEncoding::default(),
        Ok(_) => panic!("MDOC_BENCH_SIGNATURE_ENCODING must be canonical or affine-ers"),
    };
    let count = std::env::var("MDOC_BENCH_ATTRIBUTES")
        .unwrap_or_else(|_| "2".into())
        .parse::<usize>()
        .unwrap();
    let samples = std::env::var("MDOC_BENCH_SAMPLES")
        .unwrap_or_else(|_| "8".into())
        .parse::<usize>()
        .unwrap();
    assert!((1..=4).contains(&count) && samples >= 2);
    let data = &TEST_DATA;
    let resized = std::env::var("MDOC_BENCH_MSO_BYTES")
        .ok()
        .map(|s| with_mso_size(data.mdoc, s.parse().unwrap()).unwrap());
    let credential = resized
        .as_ref()
        .map_or(data.mdoc, |(bytes, _)| bytes.as_slice());
    let (_, original, now) = parse_test_data::<4, RuntimeNat<4>>(data);
    let parsed = if resized.is_some() {
        parse_mdoc::<RuntimeNat<4>>(credential, data.transcript, data.doc_type).unwrap()
    } else {
        original
    };
    let (pkx, pky) = resized.as_ref().map_or((data.pkx, data.pky), |(_, key)| {
        (key.0.as_str(), key.1.as_str())
    });
    let attrs = parsed
        .attrs
        .iter()
        .cycle()
        .take(count)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect::<Vec<_>>();
    let provided = if let Ok(path) = std::env::var("MDOC_BENCH_ARCHIVE") {
        read_next(File::open(path).unwrap()).unwrap()
    } else {
        compile_parser_free_next(count).unwrap()
    };
    assert_eq!(provided.spec().num_attributes, count);
    if let Ok(path) = std::env::var("MDOC_BENCH_SAVE_ARCHIVE") {
        write_next(File::create(path).unwrap(), &provided).unwrap();
    }
    let (signature, hash) = decompress_circuits(
        provided.compressed(),
        &P256Field::new(),
        &Gf2_128Field::new(),
    )
    .unwrap();
    let geometry = single_commitment::proof_geometry_with_encoding(
        provided.spec(),
        &signature,
        &hash,
        encoding,
    )
    .unwrap();
    eprintln!(
        "single binary commitment: encoding={encoding:?}, input_log={}, rows={}, binary layers={}, signature layers={}, K={}, N={}, s={}, T={}",
        geometry.binary().sumcheck().layers().last().unwrap(),
        geometry.polygero().nrow(),
        geometry.binary().sumcheck().layers().len(),
        geometry.signature().layers().len(),
        geometry.config().k, geometry.config().n, geometry.config().s, geometry.config().t,
    );
    println!("attributes,sample,prover_ms,verifier_ms,proof_bytes,prover_heap,verifier_heap");
    let mut times = Vec::new();
    for sample in 0..samples {
        memory::reset_peak();
        let prover_base = memory::get_current_allocated();
        let start = Instant::now();
        let proof = single_commitment::run_mdoc_prover_inner_with_encoding(
            provided.spec(),
            provided.compressed(),
            credential,
            pkx,
            pky,
            data.transcript,
            &attrs,
            now,
            data.doc_type,
            encoding,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
        let prover = start.elapsed().as_secs_f64() * 1000.0;
        let prover_heap = memory::get_peak_allocated().saturating_sub(prover_base);
        memory::reset_peak();
        let verifier_base = memory::get_current_allocated();
        let verify_start = Instant::now();
        single_commitment::run_mdoc_verifier_with_encoding(
            provided.spec(),
            provided.compressed(),
            pkx,
            pky,
            data.transcript,
            &attrs,
            now,
            data.doc_type,
            &proof,
            encoding,
        )
        .unwrap();
        let verifier = verify_start.elapsed().as_secs_f64() * 1000.0;
        let verifier_heap = memory::get_peak_allocated().saturating_sub(verifier_base);
        println!(
            "{count},{sample},{prover:.6},{verifier:.6},{},{prover_heap},{verifier_heap}",
            proof.len()
        );
        if sample > 0 {
            times.push((prover, verifier));
        }
        if sample + 1 == samples {
            let mut bad = proof;
            *bad.last_mut().unwrap() ^= 1;
            assert!(single_commitment::run_mdoc_verifier_with_encoding(
                provided.spec(),
                provided.compressed(),
                pkx,
                pky,
                data.transcript,
                &attrs,
                now,
                data.doc_type,
                &bad,
                encoding
            )
            .is_err());
        }
    }
    let median = |mut xs: Vec<f64>| {
        xs.sort_by(f64::total_cmp);
        let n = xs.len();
        if !n.is_multiple_of(2) {
            xs[n / 2]
        } else {
            (xs[n / 2 - 1] + xs[n / 2]) / 2.0
        }
    };
    eprintln!(
        "single-commitment median: prover_ms={:.3}, verifier_ms={:.3}",
        median(times.iter().map(|x| x.0).collect()),
        median(times.iter().map(|x| x.1).collect())
    );
}
