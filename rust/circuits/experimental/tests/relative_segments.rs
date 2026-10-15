// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
#[path = "../../../experiments/mldsa/relative_segments.rs"]
mod relative;
use std::time::Instant;

// Read-only historical serialization adapter, so old period-6 files retain
// their original field encoding and ID. No arithmetic or production use.
struct HistoricalFp24Ext6;
impl core_algebra::BareField for HistoricalFp24Ext6 {
    type E = [u8; 24];
}
impl core_proto::SerializableField for HistoricalFp24Ext6 {
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        24
    }
    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        dst.copy_from_slice(e);
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<Self::E, String> {
        let a: [u8; 24] = b
            .try_into()
            .map_err(|_| "invalid legacy coefficient length")?;
        if a.chunks_exact(4)
            .any(|c| u32::from_le_bytes(c.try_into().unwrap()) >= 8_380_417)
        {
            return Err("noncanonical legacy coefficient".into());
        }
        Ok(a)
    }
    fn serialized_mone(&self) -> Vec<u8> {
        let mut a = vec![0; 24];
        a[..4].copy_from_slice(&8_380_416u32.to_le_bytes());
        a
    }
}

fn check_id<F: core_proto::SerializableField>(
    f: &F,
    fid: core_proto::FieldID,
    bytes: &[u8],
    id: [u8; 32],
) {
    let (c, tail) = core_proto::reader::CircuitReader::new(f, fid)
        .from_bytes(bytes, true)
        .unwrap();
    assert!(tail.is_empty());
    assert_eq!(c.id, id);
}

#[test]
#[ignore = "offline relative segment format sweep"]
fn relative_segment_sweep() {
    let name = std::env::var("REL_DATASET").unwrap();
    let path = std::env::var("REL_CIRCUIT").unwrap();
    let size: usize = std::env::var("REL_FIELD_BYTES").unwrap().parse().unwrap();
    let dir = std::env::var("REL_OUT").unwrap();
    std::fs::create_dir_all(&dir).unwrap();
    let bytes = std::fs::read(&path).unwrap();
    let original = relative::PlainFile::read_lfc2(&bytes, size).unwrap();
    assert_eq!(original.lfc2(), bytes);
    let (all, boundary, interior) = relative::boundary_counts(&original);
    let check = |b: &[u8]| match name.as_str() {
        "mldsa44" | "mldsa65" | "mldsa44_source" | "mldsa65_source" => check_id(
            &circuits_experimental::mldsa::algebra::RuntimeFp24Ext6::new(),
            core_proto::FieldID::None,
            b,
            original.id,
        ),
        "mdoc_hash2" | "mdoc_hash2_whole" => check_id(
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            core_proto::FieldID::Gf2_128,
            b,
            original.id,
        ),
        "mdoc_sig" => check_id(
            &runtime_algebra::p256::P256Field::new(),
            core_proto::FieldID::P256,
            b,
            original.id,
        ),
        "historical44_whole"
        | "historical44_shape"
        | "historical44_boundary32"
        | "historical44_boundary128" => check_id(
            &HistoricalFp24Ext6,
            core_proto::FieldID::None,
            b,
            original.id,
        ),
        _ => panic!("unknown dataset"),
    };
    check(&bytes);
    let mut ranked = original.clone();
    for l in &mut ranked.layers {
        l.rank_deltas();
    }
    let ranked_bytes = ranked.lfc2();
    original.assert_same(&ranked);
    check(&ranked_bytes);
    println!(
        "REL_RANK_CONTROL dataset={name} raw={} z22={}",
        ranked_bytes.len(),
        zstd::bulk::compress(&ranked_bytes, 22).unwrap().len()
    );
    println!("REL_BASE dataset={name} raw={} z22={} deltas={all} boundary_only={boundary} interior={interior} segments={} tokens={}",bytes.len(),zstd::bulk::compress(&bytes,22).unwrap().len(),original.layers.iter().map(|l|l.segments.len()).sum::<usize>(),original.layers.iter().map(|l|l.tokens.len()).sum::<usize>());
    let widths: Vec<usize> = std::env::var("REL_WIDTHS")
        .unwrap_or_else(|_| "0,8,32,128".into())
        .split(',')
        .map(|v| v.parse().unwrap())
        .collect();
    for width in widths {
        for all in [false, true] {
            for pool in [false, true] {
                let label = format!(
                    "{}-{}-w{width}",
                    if all { "all" } else { "first" },
                    if pool { "pool" } else { "inline" }
                );
                let start = Instant::now();
                let (b, s) = relative::encode(&original, all, pool, width);
                let encode_ms = start.elapsed().as_secs_f64() * 1000.;
                let mut times = Vec::new();
                let mut decoded = None;
                for _ in 0..5 {
                    let start = Instant::now();
                    let out = relative::decode(&b).unwrap();
                    let lfc2 = out.lfc2();
                    times.push(start.elapsed().as_secs_f64() * 1000.);
                    decoded = Some((out, lfc2));
                }
                times.sort_by(f64::total_cmp);
                let (out, lfc2) = decoded.unwrap();
                original.assert_same(&out);
                check(&lfc2);
                let compressed = zstd::bulk::compress(&b, 22).unwrap();
                std::fs::write(format!("{dir}/{name}-{label}.lfr1"), &b).unwrap();
                std::fs::write(format!("{dir}/{name}-{label}.lfr1.zst"), &compressed).unwrap();
                if width == 0 && !all && pool {
                    std::fs::write(format!("{dir}/{name}-decoded.lfc2"), &lfc2).unwrap();
                }
                println!("REL_RESULT dataset={name} variant={label} raw={} z22={} deltas={} cores={} references={} tokens={} delta_bytes={} segment_bytes={} reference_bytes={} offset_bytes={} token_bytes={} original_segments={} shared_nontrivial={} encode_ms={encode_ms:.3} decode_ms={:.3} decoded_lfc2={} exact_stream=1",b.len(),compressed.len(),s.deltas,s.cores,s.references,s.tokens,s.delta_bytes,s.segment_bytes,s.reference_bytes,s.offset_bytes,s.token_bytes,s.original_segments,s.shared_nontrivial_segments,times[2],lfc2.len());
            }
        }
    }
}

fn load_bench<F: core_proto::SerializableField>(f: &F, field: core_proto::FieldID) {
    let name = std::env::var("REL_DATASET").unwrap();
    let baseline = std::fs::read(std::env::var("REL_CIRCUIT").unwrap()).unwrap();
    let relative = std::fs::read(std::env::var("REL_RELATIVE").unwrap()).unwrap();
    let reader = core_proto::reader::CircuitReader::new(f, field);
    let mut base_times = Vec::new();
    let mut rel_times = Vec::new();
    for _ in 0..7 {
        let start = Instant::now();
        let (base, tail) = reader.from_bytes(&baseline, false).unwrap();
        base_times.push(start.elapsed().as_secs_f64() * 1000.);
        assert!(tail.is_empty());
        let start = Instant::now();
        let decoded = relative::decode(&relative).unwrap().lfc2();
        let (rel, tail) = reader.from_bytes(&decoded, false).unwrap();
        rel_times.push(start.elapsed().as_secs_f64() * 1000.);
        assert!(tail.is_empty());
        assert_eq!(core_proto::circuit::compute_id(f, &base.raw), base.id);
        assert_eq!(core_proto::circuit::compute_id(f, &rel.raw), base.id);
        assert_eq!(rel.id, base.id);
    }
    base_times.sort_by(f64::total_cmp);
    rel_times.sort_by(f64::total_cmp);
    println!("REL_LOAD dataset={name} baseline_ms={:.3} relative_adapter_ms={:.3} repeats=7 excludes_id=1",base_times[3],rel_times[3]);
}

#[test]
#[ignore = "serial loader benchmark, no overlapping compilation or compression"]
fn relative_segment_load_bench() {
    match std::env::var("REL_DATASET").unwrap().as_str() {
        "mldsa44" | "mldsa65" => load_bench(
            &circuits_experimental::mldsa::algebra::RuntimeFp24Ext6::new(),
            core_proto::FieldID::None,
        ),
        "mdoc_hash2" => load_bench(
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            core_proto::FieldID::Gf2_128,
        ),
        "mdoc_sig" => load_bench(
            &runtime_algebra::p256::P256Field::new(),
            core_proto::FieldID::P256,
        ),
        _ => panic!("unsupported loader dataset"),
    }
}
