// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Circuit identity cost on real mdoc artifacts, with compilation outside timing.
use std::{hint::black_box, time::Instant};

use longfellow_zk::{
    core::{
        algebra::SerializableField,
        proto::v2::{self, Circuit, CircuitReader, RawCircuit},
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};
use sha2::{Digest, Sha256};

// Previous identity algorithm, retained only as a benchmark baseline.
fn expanded_id<F: SerializableField>(f: &F, raw: &RawCircuit<F>) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"LFC3-v2-three-streams-v2");
    let size = |h: &mut Sha256, n: usize| h.update((n as u64).to_le_bytes());
    size(&mut h, usize::from(f.is_binary()));
    size(&mut h, f.serialized_size_bytes());
    h.update(f.serialized_mone());
    for n in [
        raw.noutput,
        raw.logv,
        raw.ninput,
        raw.npublic_input,
        raw.layers.len(),
    ] {
        size(&mut h, n);
    }
    for l in &raw.layers {
        for n in [l.nw, l.logw, 0, l.quadratic.num_terms()] {
            size(&mut h, n);
        }
        l.quadratic.for_each(|t| {
            for n in [t.g, t.l, t.r] {
                size(&mut h, n as usize);
            }
            h.update(f.to_bytes(&raw.constants[t.k as usize]));
        });
        for n in [1, l.linear.num_terms()] {
            size(&mut h, n);
        }
        l.linear.for_each(|t| {
            for n in [t.g, t.l] {
                size(&mut h, n as usize);
            }
            h.update(f.to_bytes(&raw.constants[t.k as usize]));
        });
        for n in [2, l.constant.num_terms()] {
            size(&mut h, n);
        }
        l.constant.for_each(|t| {
            size(&mut h, t.g as usize);
            h.update(f.to_bytes(&raw.constants[t.k as usize]));
        });
    }
    h.finalize().into()
}
fn measure<T>(samples: usize, mut f: impl FnMut() -> T) -> (f64, f64) {
    for _ in 0..5 {
        black_box(f());
    }
    let mut times = Vec::with_capacity(samples);
    for _ in 0..samples {
        let start = Instant::now();
        let value = black_box(f());
        // Drop circuit allocations after the measured decoder call.
        times.push(start.elapsed().as_secs_f64() * 1000.0);
        drop(value);
    }
    times.sort_by(f64::total_cmp);
    (times[times.len() / 2], times[(times.len() - 1) * 95 / 100])
}
fn report<F: SerializableField>(attrs: usize, name: &str, f: &F, payload: &[u8], samples: usize) {
    let reader = CircuitReader::new(f);
    let (circuit, tail): (Circuit<F>, _) = reader.from_bytes(payload).unwrap();
    assert!(tail.is_empty());
    assert_eq!(v2::compute_id(f, &circuit.raw), circuit.id);
    let terms: usize = circuit.raw.layers.iter().map(|l| l.num_terms()).sum();
    let mut arrays = [0usize; 4];
    for l in &circuit.raw.layers {
        for (d, s, i, t) in [
            (
                l.quadratic.deltas.len(),
                l.quadratic.segments.len(),
                l.quadratic.segments.indices().len(),
                l.quadratic.tokens.len(),
            ),
            (
                l.linear.deltas.len(),
                l.linear.segments.len(),
                l.linear.segments.indices().len(),
                l.linear.tokens.len(),
            ),
            (
                l.constant.deltas.len(),
                l.constant.segments.len(),
                l.constant.segments.indices().len(),
                l.constant.tokens.len(),
            ),
        ] {
            for (sum, n) in arrays.iter_mut().zip([d, s, i, t]) {
                *sum += n;
            }
        }
    }
    eprintln!("attributes={attrs} {name}: terms={terms}, dictionaries={}, segments={}, indices={}, tokens={}, constants={}, payload={} bytes",
        arrays[0],arrays[1],arrays[2],arrays[3],circuit.raw.constants.len(),payload.len());
    for (label, (median, p95)) in [
        (
            "segmented_id",
            measure(samples, || {
                v2::compute_id(black_box(f), black_box(&circuit.raw))
            }),
        ),
        (
            "expanded_id_baseline",
            measure(samples.min(15), || {
                expanded_id(black_box(f), black_box(&circuit.raw))
            }),
        ),
        (
            "decode_with_id",
            measure(samples, || reader.from_bytes(black_box(payload)).unwrap()),
        ),
    ] {
        println!("{attrs},{name},{label},{median:.6},{p95:.6}");
    }
}
fn main() {
    let attrs = std::env::var("CIRCUIT_ID_BENCH_ATTRIBUTES").unwrap_or_else(|_| "4".into());
    let samples = std::env::var("CIRCUIT_ID_BENCH_SAMPLES")
        .unwrap_or_else(|_| "51".into())
        .parse::<usize>()
        .unwrap();
    assert!(samples > 0);
    println!("attributes,circuit,operation,median_ms,p95_ms");
    for attrs in attrs.split(',').map(|s| s.parse::<usize>().unwrap()) {
        assert!((1..=4).contains(&attrs));
        let bytes = longfellow_zk::mdoc::compile::compile_circuits(attrs).unwrap();
        let archive = v2::archive::from_bytes(&bytes).unwrap();
        if let Some(directory) = std::env::var_os("CIRCUIT_ID_BENCH_SAVE") {
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(
                std::path::Path::new(&directory).join(format!("mdoc-{attrs}.lfa2")),
                &bytes,
            )
            .unwrap();
        }
        report(
            attrs,
            "signature",
            &P256Field::new(),
            &archive.get("sig").unwrap().payload,
            samples,
        );
        report(
            attrs,
            "hash",
            &Gf2_128Field::new(),
            &archive.get("hash").unwrap().payload,
            samples,
        );
        let compressed = zstd::encode_all(
            bytes.as_slice(),
            longfellow_zk::mdoc::circuits::config::K_ZSTD_LEVEL,
        )
        .unwrap();
        let prime = P256Field::new();
        let binary = Gf2_128Field::new();
        let (median, p95) = measure(samples, || {
            longfellow_zk::mdoc::v2::decompress_circuits(black_box(&compressed), &prime, &binary)
                .unwrap()
        });
        println!("{attrs},both,load_compressed_archive,{median:.6},{p95:.6}");
    }
}
