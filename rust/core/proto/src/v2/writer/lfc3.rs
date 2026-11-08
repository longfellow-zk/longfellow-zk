// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Write the LFC3 allocation directory before its contiguous stream payloads.
use super::CircuitWriter;
use crate::core::proto::{
    uleb::{serialize_uleb128_max4, serialize_uleb128_max4_u32},
    v2::{
        self,
        directory::{LayerDirectory, StreamDirectory, REVISION},
        Circuit, Stream,
    },
    SerializableField,
};

fn coordinate(bytes: &mut Vec<u8>, delta: u32) {
    serialize_uleb128_max4_u32(bytes, (delta << 1) ^ ((delta as i32 >> 31) as u32));
}
fn stream<T>(
    bytes: &mut Vec<u8>,
    s: &Stream<T>,
    encode: impl Fn(&mut Vec<u8>, &T),
) -> StreamDirectory {
    let start = bytes.len();
    for term in &s.deltas {
        encode(bytes, term);
    }
    for &index in s.segments.indices() {
        serialize_uleb128_max4_u32(bytes, index);
    }
    for &token in &s.tokens {
        serialize_uleb128_max4_u32(bytes, token);
    }
    StreamDirectory {
        deltas: s.deltas.len(),
        segments: s.segments.len(),
        indices: s.segments.indices().len(),
        tokens: s.tokens.len(),
        terms: s.num_terms(),
        bytes: bytes.len() - start,
    }
}
pub(super) fn to_bytes<F: SerializableField>(
    writer: &CircuitWriter<'_, F>,
    c: &Circuit<F>,
) -> Vec<u8> {
    assert_eq!(
        c.id,
        v2::compute_id(writer.f, &c.raw),
        "v2 writer requires the semantic circuit ID"
    );
    let mut payload = Vec::new();
    for k in &c.raw.constants {
        payload.extend_from_slice(&writer.f.to_bytes(k));
    }
    let directory: Vec<_> = c
        .raw
        .layers
        .iter()
        .map(|layer| LayerDirectory {
            nw: layer.nw,
            streams: [
                stream(&mut payload, &layer.quadratic, |b, t| {
                    coordinate(b, t.g);
                    coordinate(b, t.l);
                    coordinate(b, t.r);
                    serialize_uleb128_max4_u32(b, t.k);
                }),
                stream(&mut payload, &layer.linear, |b, t| {
                    coordinate(b, t.g);
                    coordinate(b, t.l);
                    serialize_uleb128_max4_u32(b, t.k);
                }),
                stream(&mut payload, &layer.constant, |b, t| {
                    coordinate(b, t.g);
                    serialize_uleb128_max4_u32(b, t.k);
                }),
            ],
        })
        .collect();
    let mut bytes = Vec::new();
    bytes.extend_from_slice(v2::encoding::MAGIC);
    bytes.extend_from_slice(REVISION);
    for n in [
        writer.field_id as usize,
        c.raw.noutput,
        1,
        c.raw.npublic_input,
        c.raw.ninput,
        c.raw.layers.len(),
        c.raw.constants.len(),
    ] {
        serialize_uleb128_max4(&mut bytes, n);
    }
    for layer in &directory {
        serialize_uleb128_max4(&mut bytes, layer.nw);
        for s in layer.streams {
            for n in s.counts() {
                serialize_uleb128_max4(&mut bytes, n);
            }
        }
    }
    for layer in &c.raw.layers {
        for segments in [
            &layer.quadratic.segments,
            &layer.linear.segments,
            &layer.constant.segments,
        ] {
            for segment in segments.iter() {
                serialize_uleb128_max4(&mut bytes, segment.len());
            }
        }
    }
    bytes.extend_from_slice(&payload);
    bytes.extend_from_slice(&c.id);
    bytes
}
