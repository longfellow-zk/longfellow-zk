//! Fixed-traversal control: difference the interleaved key, not its coordinates.
//! Trusted-input experiment only; see the parent module's decoder limitations.
use std::{collections::HashSet, time::Instant};

use super::{get, header, put, terms, T};
use core_algebra::SerializableField;
use core_proto::{
    circuit::{compute_id, Circuit, Layer, RawCircuit},
    FieldID, TermDelta,
};

fn spread(mut x: u64) -> u64 {
    x &= 0xffff_ffff;
    x = (x | (x << 16)) & 0x0000_ffff_0000_ffff;
    x = (x | (x << 8)) & 0x00ff_00ff_00ff_00ff;
    x = (x | (x << 4)) & 0x0f0f_0f0f_0f0f_0f0f;
    x = (x | (x << 2)) & 0x3333_3333_3333_3333;
    (x | (x << 1)) & 0x5555_5555_5555_5555
}

fn compact(mut x: u64) -> u32 {
    x &= 0x5555_5555_5555_5555;
    x = (x | (x >> 1)) & 0x3333_3333_3333_3333;
    x = (x | (x >> 2)) & 0x0f0f_0f0f_0f0f_0f0f;
    x = (x | (x >> 4)) & 0x00ff_00ff_00ff_00ff;
    x = (x | (x >> 8)) & 0x0000_ffff_0000_ffff;
    (x | (x >> 16)) as u32
}

fn key(h0: u32, h1: u32) -> u64 {
    spread(u64::from(h0)) | (spread(u64::from(h1)) << 1)
}

// Match LFC1's sign/magnitude zigzag convention exactly (negative 1 => 3).
fn signed(d: u32) -> u64 {
    let d = i64::from(d as i32);
    if d < 0 {
        (-2 * d + 1) as u64
    } else {
        (2 * d) as u64
    }
}
fn unsigned(d: u64) -> u32 {
    if d & 1 == 1 {
        0u32.wrapping_sub((d >> 1) as u32)
    } else {
        (d >> 1) as u32
    }
}

fn put_number(out: &mut Vec<u8>, mut x: u64, width: usize, variable: bool) {
    if variable {
        while x >= 128 {
            out.push(x as u8 | 128);
            x >>= 7;
        }
        out.push(x as u8);
    } else {
        assert!(x < (1u64 << (8 * width)));
        out.extend_from_slice(&x.to_le_bytes()[..width]);
    }
}

fn get_number(input: &mut &[u8], width: usize, variable: bool) -> u64 {
    if variable {
        let mut value = 0;
        for shift in (0..70).step_by(7) {
            let b = input[0];
            *input = &input[1..];
            value |= u64::from(b & 127) << shift;
            if b < 128 {
                return value;
            }
        }
        panic!("invalid varint");
    }
    let mut bytes = [0; 8];
    bytes[..width].copy_from_slice(&input[..width]);
    *input = &input[width..];
    u64::from_le_bytes(bytes)
}

fn encode<F: SerializableField>(
    f: &F,
    c: &Circuit<F>,
    ts: &[Vec<T>],
    morton: bool,
    variable: bool,
) -> Vec<u8> {
    let mut out = header(f, c);
    out[..4].copy_from_slice(&[b'M', b'K', morton as u8, variable as u8]);
    for layer in ts.iter().rev() {
        put(&mut out, layer.len() as u32);
        let mut prev = [0; 3];
        let mut prev_key = 0;
        for t in layer {
            put_number(&mut out, signed(t[0].wrapping_sub(prev[0])), 3, variable);
            if morton {
                let z = key(t[1], t[2]);
                assert!(z >= prev_key, "original traversal must be absolute Morton");
                put_number(&mut out, z - prev_key, 6, variable);
                prev_key = z;
            } else {
                put_number(&mut out, signed(t[1].wrapping_sub(prev[1])), 3, variable);
                put_number(&mut out, signed(t[2].wrapping_sub(prev[2])), 3, variable);
            }
            put_number(&mut out, u64::from(t[3]), 3, variable);
            prev.copy_from_slice(&t[..3]);
        }
    }
    out
}

fn decode<F: SerializableField>(f: &F, bytes: &[u8]) -> Circuit<F> {
    assert_eq!(&bytes[..2], b"MK");
    let morton = bytes[2] != 0;
    let variable = bytes[3] != 0;
    let mut input = &bytes[4..];
    let ninput = get(&mut input) as usize;
    let npublic_input = get(&mut input) as usize;
    let noutput = get(&mut input) as usize;
    let logv = get(&mut input) as usize;
    let subfield_boundary = get(&mut input) as usize;
    let nl = get(&mut input) as usize;
    let nk = get(&mut input) as usize;
    let mut constants = Vec::new();
    let width = f.serialized_size_bytes();
    for _ in 0..nk {
        constants.push(f.bytes_to_element(&input[..width]).ok().unwrap());
        input = &input[width..];
    }
    let id: [u8; 32] = input[..32].try_into().unwrap();
    input = &input[32..];
    let geometry: Vec<_> = (0..nl)
        .map(|_| (get(&mut input) as usize, get(&mut input) as usize))
        .collect();
    let mut layers = Vec::new();
    for &(nw, logw) in geometry.iter().rev() {
        let count = get(&mut input) as usize;
        let mut ds = Vec::with_capacity(count);
        let mut previous = [0u32; 3];
        let mut prev_key = 0u64;
        for _ in 0..count {
            let dg = unsigned(get_number(&mut input, 3, variable));
            let mut now = [previous[0].wrapping_add(dg), 0, 0];
            if morton {
                prev_key = prev_key
                    .checked_add(get_number(&mut input, 6, variable))
                    .unwrap();
                now[1] = compact(prev_key);
                now[2] = compact(prev_key >> 1);
            } else {
                now[1] = previous[1].wrapping_add(unsigned(get_number(&mut input, 3, variable)));
                now[2] = previous[2].wrapping_add(unsigned(get_number(&mut input, 3, variable)));
            }
            let k_index = get_number(&mut input, 3, variable).try_into().unwrap();
            ds.push(TermDelta {
                g: dg,
                h: [
                    now[1].wrapping_sub(previous[1]),
                    now[2].wrapping_sub(previous[2]),
                ],
                k_index,
            });
            previous = now;
        }
        layers.push(Layer::new_compressed(nw, logw, vec![ds], vec![0]));
    }
    assert!(input.is_empty());
    let raw = RawCircuit {
        ninput,
        npublic_input,
        noutput,
        logv,
        subfield_boundary,
        constants,
        layers,
    };
    assert_eq!(compute_id(f, &raw), id);
    Circuit { raw, id }
}

pub(super) fn analyze<F: SerializableField>(f: &F, c: &Circuit<F>, field_id: FieldID) {
    let ts = terms(c);
    let writer = core_proto::writer::CircuitWriter::new(f, field_id);
    let original = writer.to_bytes_lfc1(c);
    super::sizes("canonical_LFC1", &original);
    let mut raw = HashSet::new();
    let mut morton = HashSet::new();
    let mut raw_coordinates = HashSet::new();
    let mut morton_coordinates = HashSet::new();
    let mut raw_chunks = HashSet::new();
    let mut morton_chunks = HashSet::new();
    let mut nchunks = 0;
    for layer in &ts {
        let mut previous = [0; 3];
        let mut prev_key = 0;
        let mut rseq = Vec::new();
        let mut mseq = Vec::new();
        for t in layer {
            let z = key(t[1], t[2]);
            assert!(z >= prev_key);
            let r = [
                signed(t[0].wrapping_sub(previous[0])),
                signed(t[1].wrapping_sub(previous[1])),
                signed(t[2].wrapping_sub(previous[2])),
                u64::from(t[3]),
            ];
            let m = [r[0], z - prev_key, u64::from(t[3])];
            raw.insert(r);
            morton.insert(m);
            raw_coordinates.insert([r[0], r[1], r[2]]);
            morton_coordinates.insert([m[0], m[1]]);
            rseq.push(r);
            mseq.push(m);
            previous.copy_from_slice(&t[..3]);
            prev_key = z;
        }
        nchunks += rseq.len() / 32;
        for chunk in rseq.chunks_exact(32) {
            raw_chunks.insert(chunk.to_vec());
        }
        for chunk in mseq.chunks_exact(32) {
            morton_chunks.insert(chunk.to_vec());
        }
    }
    println!(
        "KEY_DELTAS original_records={} morton_records={} original_coordinate_tuples={} morton_coordinate_tuples={} chunks32={nchunks} original_unique_chunks={} morton_unique_chunks={}",
        raw.len(),
        morton.len(),
        raw_coordinates.len(),
        morton_coordinates.len(),
        raw_chunks.len(),
        morton_chunks.len()
    );
    for variable in [false, true] {
        for morton in [false, true] {
            let label = format!(
                "{}_{}",
                if morton {
                    "morton_key"
                } else {
                    "raw_coordinates"
                },
                if variable { "uleb" } else { "fixed12" }
            );
            let bytes = encode(f, c, &ts, morton, variable);
            super::sizes(&label, &bytes);
            let packed = zstd::bulk::compress(&bytes, 16).unwrap();
            let mut times = Vec::new();
            for _ in 0..3 {
                let start = Instant::now();
                let unpacked = zstd::bulk::decompress(&packed, bytes.len()).unwrap();
                let recovered = decode(f, &unpacked);
                times.push(start.elapsed().as_secs_f64() * 1000.);
                assert_eq!(writer.to_bytes_lfc1(&recovered), original);
            }
            times.sort_by(f64::total_cmp);
            println!(
                "KEY_ROUNDTRIP {label}: exact_lfc1=true exact_id=true no_sort=true decode_zstd16_hash_median_ms={:.3}",
                times[1]
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn morton_key_roundtrip_and_comparator() {
        let points = [0, 1, 2, 3, 255, 256, 65535, 65536, 0xffffff, u32::MAX];
        for &a in &points {
            for &b in &points {
                let z = key(a, b);
                assert_eq!((compact(z), compact(z >> 1)), (a, b));
            }
        }
        for &a in &points {
            for &b in &points {
                for &c in &points {
                    for &d in &points {
                        assert_eq!(
                            key(a, b).cmp(&key(c, d)),
                            super::super::cmp_coordinates(&[0, a, b, 0], &[0, c, d, 0])
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn numeric_encodings_roundtrip() {
        for d in [0, 1, 123456, u32::MAX, u32::MAX - 654321] {
            assert_eq!(unsigned(signed(d)), d);
        }
        for value in [0, 127, 128, 0xffffff, 0xffffffffffff, u64::MAX] {
            let mut bytes = Vec::new();
            put_number(&mut bytes, value, 6, true);
            let mut input = bytes.as_slice();
            assert_eq!(get_number(&mut input, 6, true), value);
            assert!(input.is_empty());
        }
    }
}
