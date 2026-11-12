// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::CircuitReader;
use crate::{
    core::proto::{
        serialize_uleb128_max4,
        v2::{self, limits::*},
        FieldID,
    },
    runtime::algebra::gf2_128::Gf2_128Field,
};

fn bytes(
    header: [usize; 7],
    layers: &[(usize, [[usize; 6]; 3])],
    lengths: &[usize],
    payload: &[u8],
) -> Vec<u8> {
    let mut out = b"LFC3DIR1".to_vec();
    for n in header {
        serialize_uleb128_max4(&mut out, n);
    }
    for (nw, streams) in layers {
        serialize_uleb128_max4(&mut out, *nw);
        for s in streams {
            for &n in s {
                serialize_uleb128_max4(&mut out, n);
            }
        }
    }
    for &n in lengths {
        serialize_uleb128_max4(&mut out, n);
    }
    out.extend_from_slice(payload);
    out
}
fn header(layers: usize) -> [usize; 7] {
    [FieldID::Gf2_128 as usize, 1, 1, 0, 1, layers, 0]
}
fn reject(data: &[u8], error: &str) {
    let f = Gf2_128Field::new();
    let result = CircuitReader::new(&f, FieldID::Gf2_128).from_bytes(data, false);
    let err = match result {
        Ok(_) => panic!("accepted malformed directory"),
        Err(e) => e,
    };
    assert!(err.contains(error), "expected {error}, got {err}");
}

#[test]
fn rejects_excessive_header_counts_before_payload() {
    for (index, limit) in [
        (1, MAX_TOTAL_WIRES),
        (3, MAX_TOTAL_WIRES),
        (4, MAX_TOTAL_WIRES),
        (5, MAX_LAYERS),
        (6, MAX_TOTAL_TERMS),
    ] {
        let mut h = header(0);
        h[index] = limit + 1;
        reject(&bytes(h, &[], &[], &[]), "excessive");
    }
}
#[test]
fn unused_metadata_is_included_in_directory_totals() {
    for (index, count) in [(1, MAX_METADATA_BYTES / 80), (3, MAX_METADATA_BYTES / 4)] {
        let mut streams = [[0usize; 6]; 3];
        for s in &mut streams {
            s[index] = count;
            s[5] = s[3];
        }
        reject(
            &bytes(header(1), &[(1, streams)], &[], &[]),
            "segment/token metadata",
        );
    }
    let mut h = header(6);
    h[5] = 6;
    let mut layers = vec![(MAX_TOTAL_WIRES / 4, [[0; 6]; 3]); 5];
    layers.push((1, [[0; 6]; 3]));
    reject(&bytes(h, &layers, &[], &[]), "total wires");
}
#[test]
fn stored_and_expanded_terms_share_global_limits() {
    let mut streams = [[0usize; 6]; 3];
    streams[0] = [0, 0, MAX_TOTAL_TERMS + 1, 0, 0, MAX_TOTAL_TERMS + 1];
    reject(&bytes(header(1), &[(1, streams)], &[], &[]), "total terms");
    streams[0] = [0, 0, 0, 0, MAX_TOTAL_TERMS + 1, 0];
    reject(&bytes(header(1), &[(1, streams)], &[], &[]), "total terms");
}
#[test]
fn segment_lengths_must_exactly_cover_the_declared_flat_array() {
    let streams = [[1, 2, 2, 0, 0, 6], [0; 6], [0; 6]];
    reject(
        &bytes(header(1), &[(1, streams)], &[1, 0], &[]),
        "do not cover",
    );
    reject(
        &bytes(header(1), &[(1, streams)], &[2, 1], &[]),
        "exceed index count",
    );
    reject(
        &bytes(header(1), &[(1, streams)], &[3, 0], &[]),
        "excessive segment length",
    );
}
#[test]
fn zero_term_limit_still_enforces_metadata_limits() {
    let f = Gf2_128Field::new();
    let streams = [[0, MAX_METADATA_BYTES / 80 + 1, 0, 0, 0, 0], [0; 6], [0; 6]];
    let data = bytes(header(1), &[(1, streams)], &[], &[]);
    assert!(CircuitReader::new(&f, FieldID::Gf2_128)
        .with_total_term_limit(0)
        .from_bytes(&data, false)
        .is_err());
}
#[test]
fn flat_segments_roundtrip_over_one_byte_buffers_without_changing_identity() {
    let f = Gf2_128Field::new();
    let raw = v2::RawCircuitBuilder {
        ninput: 1,
        npublic_input: 0,
        noutput: 1,
        logv: 0,
        constants: vec![],
        layers: vec![v2::Layer::with_assertions(
            1,
            v2::Stream {
                deltas: vec![],
                segments: vec![vec![], vec![]].into(),
                tokens: vec![0, 1, 0],
            },
            v2::Stream::default(),
            v2::Stream::default(),
            |_| false,
        )],
    }
    .build();
    let c = v2::Circuit::new(v2::compute_id(&f, &raw), raw);
    let writer = v2::CircuitWriter::new(&f, FieldID::Gf2_128);
    let encoded = writer.to_bytes(&c);
    let reader = CircuitReader::new(&f, FieldID::Gf2_128).with_total_term_limit(0);
    let mut input = std::io::BufReader::with_capacity(1, encoded.as_slice());
    let decoded = reader.from_stream(&mut input, true).unwrap();
    assert_eq!(decoded.id, c.id);
    assert_eq!(writer.to_bytes(&decoded), encoded);
    assert_eq!(decoded.raw.layers[0].quadratic.segments.ends(), [0, 0]);
    for end in 0..encoded.len() {
        assert!(reader.from_bytes(&encoded[..end], true).is_err());
    }
}

#[test]
fn truncated_large_payload_is_rejected_before_reserving_circuit_arrays() {
    let f = Gf2_128Field::new();
    let mut streams = [[0; 6]; 3];
    streams[0] = [MAX_TOTAL_TERMS, 0, 0, 0, 0, MAX_ARCHIVE_BYTES];
    let data = bytes(header(1), &[(1, streams)], &[], &[]);
    reject(&data, "Incomplete LFC3 payload");
    let mut input = std::io::BufReader::with_capacity(1, data.as_slice());
    assert!(CircuitReader::new(&f, FieldID::Gf2_128)
        .from_stream(&mut input, false)
        .is_err());
}
