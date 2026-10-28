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

use super::CircuitWriter;
use crate::core::proto::{
    circuit::Circuit,
    uleb::{serialize_uleb128_max4, serialize_uleb128_max4_u32},
    SerializableField,
};

#[inline(always)]
fn zigzag_encode_delta(delta: u32) -> u32 {
    (delta << 1) ^ ((delta as i32 >> 31) as u32)
}

pub(super) fn to_bytes_lfc2<F: SerializableField>(
    writer: &CircuitWriter<'_, F>,
    sc_c: &Circuit<F>,
) -> Vec<u8> {
    let mut bytes = Vec::new();

    // Write header
    let separated = sc_c.raw.layers.iter().any(|l| l.affine().is_some());
    let linear_assertions = sc_c.raw.layers.iter().any(|l| l.has_linear_assertions());
    let coefficients = sc_c.raw.layers.iter().any(|l| l.coefficients().is_some());
    assert!(!coefficients || separated, "LFD3 requires degree streams");
    bytes.extend_from_slice(if linear_assertions {
        b"LFD4"
    } else if coefficients {
        b"LFD3"
    } else if separated {
        b"LFD2"
    } else {
        b"LFC2"
    }); // magic header
    serialize_uleb128_max4(&mut bytes, writer.field_id as usize);
    serialize_uleb128_max4(&mut bytes, sc_c.raw.noutput); // sc_c.nv
    serialize_uleb128_max4(&mut bytes, 1); // sc_c.nc
    serialize_uleb128_max4(&mut bytes, sc_c.raw.npublic_input); // sc_c.npub_in
    serialize_uleb128_max4(&mut bytes, sc_c.raw.subfield_boundary);
    serialize_uleb128_max4(&mut bytes, sc_c.raw.ninput); // sc_c.ninputs
    serialize_uleb128_max4(&mut bytes, sc_c.raw.layers.len());

    // Write constants
    serialize_uleb128_max4(&mut bytes, sc_c.raw.constants.len());
    for v in &sc_c.raw.constants {
        writer.serialize_elt(&mut bytes, v);
    }

    // Serialize each layer
    for layer in &sc_c.raw.layers {
        assert_eq!(layer.affine().is_some(), separated, "mixed circuit formats");
        assert!(
            crate::core::proto::sane_logw(layer.logw),
            "layer logw must be sane"
        );
        serialize_uleb128_max4(&mut bytes, layer.logw);
        serialize_uleb128_max4(&mut bytes, layer.nw);

        for (arity, layer) in std::iter::once((2, layer)).chain(
            layer
                .affine()
                .into_iter()
                .flat_map(|streams| [(1, &streams[0]), (0, &streams[1])]),
        ) {
            assert_eq!(
                layer.coefficients().is_some(),
                coefficients,
                "mixed coefficient formats"
            );
            // Write the deduplicated delta table for this layer to disk.
            serialize_uleb128_max4(&mut bytes, layer.deltas().len());
            for term in layer.deltas() {
                serialize_uleb128_max4_u32(&mut bytes, zigzag_encode_delta(term.g));
                if arity >= 1 {
                    serialize_uleb128_max4_u32(&mut bytes, zigzag_encode_delta(term.h[0]));
                }
                if arity >= 2 {
                    serialize_uleb128_max4_u32(&mut bytes, zigzag_encode_delta(term.h[1]));
                }
                serialize_uleb128_max4_u32(&mut bytes, term.k_index);
            }

            // Write the segments dictionary (sequences of delta indices).
            serialize_uleb128_max4(&mut bytes, layer.delta_segments().len());
            for seg in layer.delta_segments() {
                serialize_uleb128_max4(&mut bytes, seg.len());
                for &idx in seg {
                    serialize_uleb128_max4_u32(&mut bytes, idx);
                }
            }

            // Write the token sequence indicating which segment dictionary entries to execute.
            serialize_uleb128_max4(&mut bytes, layer.delta_tokens().len());
            for &tok in layer.delta_tokens() {
                serialize_uleb128_max4_u32(&mut bytes, tok);
            }
            if let Some(c) = layer.coefficients() {
                use crate::core::proto::fixed::UnitTerms;
                match &c.units {
                    UnitTerms::Quadratic(s) => {
                        assert_eq!(arity, 2);
                        write_fixed(&mut bytes, s);
                    }
                    UnitTerms::Linear(s) => {
                        assert_eq!(arity, 1);
                        write_fixed(&mut bytes, s);
                    }
                    UnitTerms::Constant(s) => {
                        assert_eq!(arity, 0);
                        write_fixed(&mut bytes, s);
                    }
                }
                if arity == 2 || (arity == 1 && linear_assertions) {
                    match &c.assertions {
                        UnitTerms::Quadratic(s) => {
                            assert_eq!(arity, 2);
                            write_fixed(&mut bytes, s);
                        }
                        UnitTerms::Linear(s) => {
                            assert_eq!(arity, 1);
                            write_fixed(&mut bytes, s);
                        }
                        _ => panic!("assertion degree mismatch"),
                    }
                } else {
                    assert_eq!(c.assertions.num_terms(), 0);
                }
            }
        }
    }
    bytes.extend_from_slice(&sc_c.id);
    bytes
}

#[inline(always)]
#[must_use]
pub fn uleb128_len_u32(mut val: u32) -> u32 {
    let mut len = 1;
    while val >= 0x80 {
        val >>= 7;
        len += 1;
    }
    len
}

fn write_fixed<const N: usize>(
    bytes: &mut Vec<u8>,
    stream: &crate::core::proto::fixed::FixedStream<N>,
) {
    serialize_uleb128_max4(bytes, stream.deltas.len());
    for d in &stream.deltas {
        for &x in d {
            serialize_uleb128_max4_u32(bytes, zigzag_encode_delta(x));
        }
    }
    serialize_uleb128_max4(bytes, stream.segments.len());
    for s in &stream.segments {
        serialize_uleb128_max4(bytes, s.len());
        for &i in s {
            serialize_uleb128_max4_u32(bytes, i);
        }
    }
    serialize_uleb128_max4(bytes, stream.tokens.len());
    for &t in &stream.tokens {
        serialize_uleb128_max4_u32(bytes, t);
    }
}
