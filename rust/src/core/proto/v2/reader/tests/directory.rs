// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::super::CircuitReader;
use crate::{
    core::{
        algebra::FieldID,
        proto::{serialize_uleb128_max4, v2, v2::limits::*},
    },
    runtime::algebra::gf2_128::Gf2_128Field,
    util::ceil_log2,
};

fn bytes(
    header: [usize; 7],
    layers: &[(usize, [[usize; 6]; 3])],
    lengths: &[usize],
    payload: &[u8],
) -> Vec<u8> {
    let mut out = b"LFC3DIR3".to_vec();
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
    let result = CircuitReader::new(&f).from_bytes(data);
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
    assert!(CircuitReader::new(&f)
        .with_total_term_limit(0)
        .from_bytes(&data)
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
        layers: vec![v2::Layer::new(
            1,
            v2::Stream {
                deltas: vec![],
                segments: vec![vec![], vec![]].into(),
                tokens: vec![0, 1, 0],
            },
            v2::Stream::default(),
            v2::Stream::default(),
        )],
    }
    .build();
    let c = v2::Circuit::from_raw(&f, raw);
    let writer = v2::CircuitWriter::new(&f);
    let encoded = writer.to_bytes(&c);
    let reader = CircuitReader::new(&f).with_total_term_limit(0);
    let mut input = std::io::BufReader::with_capacity(1, encoded.as_slice());
    let decoded = reader.from_stream(&mut input).unwrap();
    assert_eq!(decoded.id, c.id);
    assert_eq!(writer.to_bytes(&decoded), encoded);
    assert_eq!(decoded.raw.layers[0].quadratic.segments.ends(), [0, 0]);
    for end in 0..encoded.len() {
        assert!(reader.from_bytes(&encoded[..end]).is_err());
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
    assert!(CircuitReader::new(&f).from_stream(&mut input).is_err());
}

#[test]
fn trusted_wire_opt_in_is_local_and_accepts_its_exact_bound() {
    let f = Gf2_128Field::new();
    let wires = MAX_TOTAL_WIRES + 1;
    let raw = v2::RawCircuitBuilder {
        ninput: wires,
        npublic_input: 0,
        noutput: wires,
        logv: ceil_log2(wires),
        constants: vec![],
        layers: vec![],
    }
    .build();
    let circuit = v2::Circuit::from_raw(&f, raw);
    let encoded = v2::CircuitWriter::new(&f).to_bytes(&circuit);
    let ordinary = CircuitReader::new(&f);
    assert!(ordinary.from_bytes(&encoded).is_err());
    let trusted = CircuitReader::new(&f).with_trusted_size_limits(wires, 0);
    let (decoded, tail) = trusted.from_bytes(&encoded).unwrap();
    assert!(tail.is_empty());
    assert_eq!(decoded.id, circuit.id);
    assert!(CircuitReader::new(&f)
        .with_trusted_size_limits(wires - 1, 0)
        .from_bytes(&encoded)
        .is_err());
    assert!(ordinary.from_bytes(&encoded).is_err());
}

#[test]
fn trusted_directory_limits_bound_wires_and_terms_independently() {
    use v2::directory::{validate, LayerDirectory, StreamDirectory};
    let large_terms = MAX_TOTAL_TERMS + 1;
    let layers = [LayerDirectory {
        nw: 2,
        streams: [
            StreamDirectory {
                terms: large_terms,
                ..Default::default()
            },
            StreamDirectory::default(),
            StreamDirectory::default(),
        ],
    }];
    let limits = SizeLimits {
        total_wires: 3,
        stored_terms: large_terms,
        expanded_terms: large_terms,
        ..SizeLimits::default()
    };
    // The directory accepts each exact bound, before decoding stream payloads.
    assert!(validate(&layers, 2, 1, 0, 0, limits).is_ok());
    assert!(validate(
        &layers,
        2,
        1,
        0,
        0,
        SizeLimits {
            total_wires: 2,
            ..limits
        }
    )
    .unwrap_err()
    .contains("total wires"));
    assert!(validate(
        &layers,
        2,
        1,
        0,
        0,
        SizeLimits {
            expanded_terms: large_terms - 1,
            ..limits
        }
    )
    .unwrap_err()
    .contains("total terms"));
    assert!(validate(
        &layers,
        2,
        1,
        3,
        3,
        SizeLimits {
            stored_terms: 2,
            ..limits
        }
    )
    .unwrap_err()
    .contains("total terms"));
}

#[test]
fn trusted_size_opt_in_preserves_metadata_and_payload_limits() {
    use v2::directory::{validate, LayerDirectory, StreamDirectory};
    let limits = SizeLimits {
        total_wires: usize::MAX,
        stored_terms: usize::MAX,
        expanded_terms: usize::MAX,
        ..SizeLimits::default()
    };
    for (stream, error) in [
        (
            StreamDirectory {
                tokens: MAX_METADATA_BYTES / 4 + 1,
                bytes: MAX_METADATA_BYTES / 4 + 1,
                ..Default::default()
            },
            "metadata",
        ),
        (
            StreamDirectory {
                indices: MAX_ARCHIVE_BYTES + 1,
                bytes: MAX_ARCHIVE_BYTES + 1,
                ..Default::default()
            },
            "payload",
        ),
    ] {
        let layers = [LayerDirectory {
            nw: 1,
            streams: [
                stream,
                StreamDirectory::default(),
                StreamDirectory::default(),
            ],
        }];
        assert!(validate(&layers, 1, 1, 0, 0, limits)
            .unwrap_err()
            .contains(error));
    }
}

#[test]
fn trusted_metadata_limit_accepts_the_exact_declared_size() {
    use v2::directory::{validate, LayerDirectory, StreamDirectory};
    let layers = [LayerDirectory {
        nw: 1,
        streams: [
            StreamDirectory {
                tokens: 1,
                bytes: 1,
                ..Default::default()
            },
            StreamDirectory::default(),
            StreamDirectory::default(),
        ],
    }];
    let metadata = std::mem::size_of::<LayerDirectory>()
        + std::mem::size_of::<v2::Layer>()
        + std::mem::size_of::<u32>();
    let limits = SizeLimits {
        metadata_bytes: metadata,
        ..SizeLimits::default()
    };
    assert!(validate(&layers, 1, 1, 0, 0, limits).is_ok());
    assert!(validate(
        &layers,
        1,
        1,
        0,
        0,
        SizeLimits {
            metadata_bytes: metadata - 1,
            ..limits
        }
    )
    .unwrap_err()
    .contains("metadata"));
    let f = Gf2_128Field::new();
    let reader = CircuitReader::new(&f)
        .with_trusted_metadata_limit(metadata)
        .with_trusted_size_limits(3, 7);
    assert_eq!(reader.limits.metadata_bytes, metadata);
    assert_eq!(reader.limits.total_wires, 3);
    assert_eq!(reader.limits.stored_terms, 7);
    assert_eq!(
        CircuitReader::new(&f).limits.metadata_bytes,
        MAX_METADATA_BYTES
    );
}
