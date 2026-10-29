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
    let classes = c.coefficient_classes;
    assert_eq!(
        c.id,
        v2::compute_id(writer.f, &c.raw, classes),
        "LFC3 writer requires a canonical LFC3 circuit ID"
    );
    let mut bytes = Vec::new();
    bytes.extend_from_slice(v2::encoding::MAGIC);
    serialize_uleb128_max4(&mut bytes, classes.bits());
    for n in [
        writer.field_id as usize,
        c.raw.noutput,
        1,
        c.raw.npublic_input,
        c.raw.subfield_boundary,
        c.raw.ninput,
        c.raw.layers.len(),
        c.raw.constants.len(),
    ] {
        serialize_uleb128_max4(&mut bytes, n);
    }
    for k in &c.raw.constants {
        writer.serialize_elt(&mut bytes, k);
    }
    for layer in &c.raw.layers {
        serialize_uleb128_max4(&mut bytes, layer.logw);
        serialize_uleb128_max4(&mut bytes, layer.nw);
        macro_rules! general {
            ($stream:expr, $($field:ident),+) => {
                stream(&mut bytes, &$stream, |bytes, term| {
                    $(coordinate(bytes, term.$field);)+
                    serialize_uleb128_max4_u32(bytes, term.k);
                });
            };
        }
        macro_rules! coordinates {
            ($stream:expr, $($field:ident),+) => {
                stream(&mut bytes, &$stream, |bytes, term| { $(coordinate(bytes, term.$field);)+ });
            };
        }
        general!(layer.quadratic, g, l, r);
        coordinates!(layer.quadratic_one, g, l, r);
        coordinates!(layer.quadratic_minus_one, g, l, r);
        coordinates!(layer.quadratic_assertions, g, l, r);
        general!(layer.linear, g, l);
        coordinates!(layer.linear_one, g, l);
        coordinates!(layer.linear_minus_one, g, l);
        coordinates!(layer.linear_assertions, g, l);
        general!(layer.constant, g);
        coordinates!(layer.constant_one, g);
        coordinates!(layer.constant_minus_one, g);
    }
    bytes.extend_from_slice(&c.id);
    bytes
}
