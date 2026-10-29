// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Write compiler-native v2 streams without legacy layer adapters.
use super::CircuitWriter;
use crate::core::proto::{
    uleb::{serialize_uleb128_max4, serialize_uleb128_max4_u32},
    v2::{self, Circuit, Stream},
    SerializableField,
};

fn coordinate(bytes: &mut Vec<u8>, delta: u32) {
    serialize_uleb128_max4_u32(bytes, (delta << 1) ^ ((delta as i32 >> 31) as u32));
}

fn stream<T>(bytes: &mut Vec<u8>, stream: &Stream<T>, encode: impl Fn(&mut Vec<u8>, &T)) {
    serialize_uleb128_max4(bytes, stream.deltas.len());
    for term in &stream.deltas {
        encode(bytes, term);
    }
    serialize_uleb128_max4(bytes, stream.segments.len());
    for segment in &stream.segments {
        serialize_uleb128_max4(bytes, segment.len());
        for &index in segment {
            serialize_uleb128_max4_u32(bytes, index);
        }
    }
    serialize_uleb128_max4(bytes, stream.tokens.len());
    for &token in &stream.tokens {
        serialize_uleb128_max4_u32(bytes, token);
    }
}

pub(super) fn to_bytes<F: SerializableField>(
    writer: &CircuitWriter<'_, F>,
    c: &Circuit<F>,
) -> Vec<u8> {
    assert_eq!(
        c.id,
        v2::compute_id(writer.f, &c.raw),
        "LFC3 writer requires a canonical LFC3 circuit ID"
    );
    let mut bytes = Vec::new();
    bytes.extend_from_slice(v2::encoding::MAGIC);
    for n in [
        writer.field_id as usize,
        c.raw.noutput,
        1,
        c.raw.npublic_input,
        c.raw.subfield_boundary,
        c.raw.ninput,
        c.raw.layers.len(),
        c.raw.constants.len() - 3,
    ] {
        serialize_uleb128_max4(&mut bytes, n);
    }
    for k in c.raw.constants.iter().skip(3) {
        writer.serialize_elt(&mut bytes, k);
    }
    for layer in &c.raw.layers {
        serialize_uleb128_max4(&mut bytes, layer.logw);
        serialize_uleb128_max4(&mut bytes, layer.nw);
        stream(&mut bytes, &layer.quadratic, |bytes, term| {
            coordinate(bytes, term.g);
            coordinate(bytes, term.l);
            coordinate(bytes, term.r);
            serialize_uleb128_max4_u32(bytes, term.k);
        });
        stream(&mut bytes, &layer.linear, |bytes, term| {
            coordinate(bytes, term.g);
            coordinate(bytes, term.l);
            serialize_uleb128_max4_u32(bytes, term.k);
        });
        stream(&mut bytes, &layer.constant, |bytes, term| {
            coordinate(bytes, term.g);
            serialize_uleb128_max4_u32(bytes, term.k);
        });
    }
    bytes.extend_from_slice(&c.id);
    bytes
}
