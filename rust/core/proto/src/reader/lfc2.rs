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

use super::CircuitReader;
use crate::{
    core::proto::{
        circuit::{Circuit, Layer, RawCircuit, TermDelta},
        uleb::{read_uleb128_max4, read_uleb128_max4_u32},
        SerializableField,
    },
    util::ceil_log2,
};

pub(super) fn from_stream_lfc2_inner<R: std::io::BufRead, F: SerializableField>(
    reader: &CircuitReader<'_, F>,
    stream: &mut R,
    enforce_circuit_id: bool,
    separated: bool,
    coefficient_separated: bool,
    linear_assertions: bool,
) -> Result<Circuit<F>, String> {
    let fid_as_size_t = read_uleb128_max4(stream)?;
    let nv = read_uleb128_max4(stream)?;
    if nv > super::MAX_WIRES {
        return Err(format!(
            "Excessive noutput count: {} (max {})",
            nv,
            super::MAX_WIRES
        ));
    }
    let logv = ceil_log2(nv);
    if !crate::core::proto::sane_logw(logv) {
        return Err(format!(
            "Circuit logv {} exceeds MAX_LOGW {} or usize bit width",
            logv,
            crate::core::proto::MAX_LOGW
        ));
    }
    let nc = read_uleb128_max4(stream)?;
    if nc != 1 {
        return Err(format!("Unsupported ncopies: expected 1, got {nc}"));
    }
    let npub_in = read_uleb128_max4(stream)?;
    if npub_in > super::MAX_WIRES {
        return Err(format!(
            "Excessive npublic_input count: {} (max {})",
            npub_in,
            super::MAX_WIRES
        ));
    }
    let subfield_boundary = read_uleb128_max4(stream)?;
    if subfield_boundary > super::MAX_WIRES {
        return Err(format!(
            "Excessive subfield_boundary: {} (max {})",
            subfield_boundary,
            super::MAX_WIRES
        ));
    }
    let ninputs = read_uleb128_max4(stream)?;
    if ninputs > super::MAX_WIRES {
        return Err(format!(
            "Excessive ninput count: {} (max {})",
            ninputs,
            super::MAX_WIRES
        ));
    }
    let nl = read_uleb128_max4(stream)?;
    if nl > super::MAX_LAYERS {
        return Err(format!(
            "Excessive layer count: {} (max {})",
            nl,
            super::MAX_LAYERS
        ));
    }

    if fid_as_size_t != reader.field_id as usize {
        return Err(format!(
            "Field ID mismatch: expected {}, got {}",
            reader.field_id as usize, fid_as_size_t
        ));
    }

    // Read constants
    let numconst = read_uleb128_max4(stream)?;
    if numconst > super::MAX_CONSTANTS {
        return Err(format!(
            "Excessive constants count: {} (max {})",
            numconst,
            super::MAX_CONSTANTS
        ));
    }
    let elt_size = SerializableField::serialized_size_bytes(reader.f);
    let mut chunk = vec![0u8; elt_size];
    let mut constants = Vec::with_capacity(numconst);
    for _ in 0..numconst {
        stream
            .read_exact(&mut chunk)
            .map_err(|e| format!("Failed to read constant: {e}"))?;
        let vv = reader
            .f
            .bytes_to_element(&chunk)
            .map_err(|e| format!("Field deserialization error: {e:?}"))?;
        constants.push(vv);
    }

    // Read layers
    let mut layers = Vec::with_capacity(nl);
    let mut total_terms = 0usize;
    for _ in 0..nl {
        let logw = read_uleb128_max4(stream)?;
        if !crate::core::proto::sane_logw(logw) {
            return Err(format!(
                "Layer logw {} exceeds MAX_LOGW {} or usize bit width",
                logw,
                crate::core::proto::MAX_LOGW
            ));
        }
        let nw = read_uleb128_max4(stream)?;
        if nw > super::MAX_LAYER_INPUTS {
            return Err(format!(
                "Excessive nw count: {} (max {})",
                nw,
                super::MAX_LAYER_INPUTS
            ));
        }

        let mut streams = Vec::new();
        for arity in if separated {
            (0..3).rev()
        } else {
            (2..3).rev()
        } {
            // 1. Read deduplicated delta table from stream
            let ndeltas = read_uleb128_max4(stream)?;
            if ndeltas > super::MAX_DELTAS {
                return Err(format!(
                    "Excessive deltas count: {} (max {})",
                    ndeltas,
                    super::MAX_DELTAS
                ));
            }
            let mut deltas = Vec::with_capacity(ndeltas);
            for _ in 0..ndeltas {
                let g = decode_delta_u32(read_uleb128_max4_u32(stream)?);
                let h0 = if arity >= 1 {
                    decode_delta_u32(read_uleb128_max4_u32(stream)?)
                } else {
                    0
                };
                let h1 = if arity >= 2 {
                    decode_delta_u32(read_uleb128_max4_u32(stream)?)
                } else {
                    0
                };
                let k_index = read_uleb128_max4_u32(stream)?;
                if k_index as usize >= constants.len() {
                    return Err(format!(
                        "v2 delta k_index out of bounds: {} >= {}",
                        k_index,
                        constants.len()
                    ));
                }
                deltas.push(TermDelta {
                    g,
                    h: [h0, h1],
                    k_index,
                });
            }

            // 2. Read segments dictionary (sequences of delta indices)
            let n_segments = read_uleb128_max4(stream)?;
            if n_segments > super::MAX_DELTAS {
                return Err(format!(
                    "Excessive segments count: {} (max {})",
                    n_segments,
                    super::MAX_DELTAS
                ));
            }
            let mut delta_segments = Vec::with_capacity(n_segments);
            for _ in 0..n_segments {
                let seg_len = read_uleb128_max4(stream)?;
                if seg_len > super::MAX_TERMS_PER_LAYER {
                    return Err(format!(
                        "Excessive segment length: {} (max {})",
                        seg_len,
                        super::MAX_TERMS_PER_LAYER
                    ));
                }
                let mut seg = Vec::with_capacity(seg_len);
                for _ in 0..seg_len {
                    let d_idx = read_uleb128_max4_u32(stream)?;
                    if d_idx as usize >= deltas.len() {
                        return Err(format!(
                            "v2 delta index out of bounds: {} >= {}",
                            d_idx,
                            deltas.len()
                        ));
                    }
                    seg.push(d_idx);
                }
                delta_segments.push(seg);
            }

            // 3. Read token sequence
            let ntokens = read_uleb128_max4(stream)?;
            if ntokens > super::MAX_TERMS_PER_LAYER {
                return Err(format!(
                    "Excessive layer token count: {} (max {})",
                    ntokens,
                    super::MAX_TERMS_PER_LAYER
                ));
            }
            let mut delta_tokens = Vec::with_capacity(ntokens);
            for _ in 0..ntokens {
                let tok = read_uleb128_max4_u32(stream)?;
                if (tok as usize) >= delta_segments.len() {
                    return Err(format!(
                        "v2 token out of bounds: {} (segments={})",
                        tok,
                        delta_segments.len()
                    ));
                }
                delta_tokens.push(tok);
            }

            let mut layer_nterms = 0usize;
            for &tok in &delta_tokens {
                layer_nterms = layer_nterms.saturating_add(delta_segments[tok as usize].len());
            }

            if layer_nterms > super::MAX_TERMS_PER_LAYER {
                return Err(format!(
                    "Excessive layer term count after expansion: {} (max {})",
                    layer_nterms,
                    super::MAX_TERMS_PER_LAYER
                ));
            }
            total_terms = total_terms.saturating_add(layer_nterms);
            if total_terms > reader.max_total_terms {
                return Err(format!(
                    "Total terms across layers {} exceeds MAX_TOTAL_TERMS {}",
                    total_terms, reader.max_total_terms
                ));
            }

            let mut part = Layer::new(nw, logw, deltas, delta_segments, delta_tokens);
            if coefficient_separated {
                use crate::core::proto::fixed::{FixedCoefficients, FixedStream, UnitTerms};
                let units = match arity {
                    2 => UnitTerms::Quadratic(read_fixed(stream)?),
                    1 => UnitTerms::Linear(read_fixed(stream)?),
                    0 => UnitTerms::Constant(read_fixed(stream)?),
                    _ => unreachable!(),
                };
                let assertions = if arity == 2 {
                    UnitTerms::Quadratic(read_fixed(stream)?)
                } else if arity == 1 && linear_assertions {
                    UnitTerms::Linear(read_fixed(stream)?)
                } else {
                    UnitTerms::Constant(FixedStream::default())
                };
                let fixed = FixedCoefficients::new(units, assertions, reader.f)?;
                for d in part.deltas() {
                    let k = &constants[d.k_index as usize];
                    if k == fixed.one() || k == fixed.zero() {
                        return Err("special coefficient in LFD3 general stream".into());
                    }
                }
                let added = fixed
                    .units
                    .num_terms()
                    .saturating_add(fixed.assertions.num_terms());
                if added > super::MAX_TERMS_PER_LAYER
                    || total_terms.saturating_add(added) > reader.max_total_terms
                {
                    return Err("LFD3 expanded term budget exceeded".into());
                }
                total_terms += added;
                part = part.with_coefficients(fixed);
            }
            streams.push(part);
        }
        let layer = streams.remove(0);
        layers.push(if separated {
            let linear = streams.remove(0);
            let constant = streams.remove(0);
            layer.with_affine(linear, constant)
        } else {
            layer
        });
    }

    // Read circuit ID (32 bytes)
    let mut id = [0u8; 32];
    stream
        .read_exact(&mut id)
        .map_err(|e| format!("Failed to read ID: {e}"))?;

    let raw = RawCircuit {
        ninput: ninputs,
        npublic_input: npub_in,
        noutput: nv,
        logv,
        subfield_boundary,
        constants,
        layers,
    };

    super::validate_raw_circuit(&raw)?;

    if separated {
        let zero = reader.f.bytes_to_element(&vec![0; elt_size])?;
        for (i, layer) in raw.layers.iter().enumerate() {
            let outputs = if i == 0 {
                raw.noutput
            } else {
                raw.layers[i - 1].nw()
            };
            if layer.num_terms() > super::MAX_TERMS_PER_LAYER {
                return Err("LFD2 layer exceeds the expanded term limit".into());
            }
            if layer.logw() != ceil_log2(layer.nw()) || layer.nw() == 0 {
                return Err("invalid LFD2 layer width".into());
            }
            for (arity, stream) in (0..=2).rev().zip(layer.streams()) {
                validate_degree_stream(stream, arity, outputs, &raw.constants, &zero)?;
                if let Some(c) = stream.coefficients() {
                    c.units.validate(outputs, layer.nw())?;
                    c.assertions.validate(outputs, layer.nw())?;
                }
            }
        }
        if raw.layers.last().is_some_and(|l| l.nw() != raw.ninput) {
            return Err("LFD2 input width mismatch".into());
        }
    }

    if enforce_circuit_id {
        let computed_id = crate::core::proto::circuit::compute_id(reader.f, &raw);
        if computed_id != id {
            return Err("Circuit ID verification failed".to_string());
        }
    }

    Ok(Circuit { raw, id })
}

/// Check translated macro runs without expanding every occurrence. Valid wire
/// labels are below 5 million, so each wrapped delta has its signed i32 meaning.
fn validate_degree_stream<F: SerializableField>(
    stream: &Layer<F>,
    arity: usize,
    outputs: usize,
    constants: &[F::E],
    zero: &F::E,
) -> Result<(), String> {
    let mut summaries = Vec::with_capacity(stream.delta_segments().len());
    for segment in stream.delta_segments() {
        let mut end = [0i64; 3];
        let mut min = [i64::MAX; 3];
        let mut max = [i64::MIN; 3];
        for &index in segment {
            let d = &stream.deltas()[index as usize];
            if arity < 2 && &constants[d.k_index as usize] == zero {
                return Err("zero coefficient in LFD2 affine stream".into());
            }
            for (j, delta) in [d.g, d.h[0], d.h[1]]
                .into_iter()
                .enumerate()
                .take(arity + 1)
            {
                end[j] += i64::from(delta as i32);
                min[j] = min[j].min(end[j]);
                max[j] = max[j].max(end[j]);
            }
        }
        summaries.push((end, min, max));
    }
    let limits = [outputs as i64, stream.nw() as i64, stream.nw() as i64];
    let mut offset = [0i64; 3];
    for &token in stream.delta_tokens() {
        if stream.delta_segments()[token as usize].is_empty() {
            continue;
        }
        let (end, min, max) = summaries[token as usize];
        for j in 0..=arity {
            if offset[j] + min[j] < 0 || offset[j] + max[j] >= limits[j] {
                return Err("LFD2 term index out of bounds".into());
            }
            offset[j] += end[j];
        }
    }
    Ok(())
}

#[inline(always)]
fn decode_delta_u32(val: u32) -> u32 {
    (val >> 1) ^ ((val & 1).wrapping_neg())
}

fn read_fixed<const N: usize, R: std::io::BufRead>(
    stream: &mut R,
) -> Result<crate::core::proto::fixed::FixedStream<N>, String> {
    use crate::core::proto::fixed::FixedStream;
    let count = read_uleb128_max4(stream)?;
    if count > super::MAX_DELTAS {
        return Err("excessive fixed deltas".into());
    }
    let mut deltas = Vec::with_capacity(count);
    for _ in 0..count {
        let mut d = [0; N];
        for x in &mut d {
            *x = decode_delta_u32(read_uleb128_max4_u32(stream)?);
        }
        deltas.push(d);
    }
    let count = read_uleb128_max4(stream)?;
    if count > super::MAX_DELTAS {
        return Err("excessive fixed segments".into());
    }
    let mut segments = Vec::with_capacity(count);
    for _ in 0..count {
        let n = read_uleb128_max4(stream)?;
        if n > super::MAX_TERMS_PER_LAYER {
            return Err("excessive fixed segment length".into());
        }
        let mut s = Vec::with_capacity(n);
        for _ in 0..n {
            let i = read_uleb128_max4_u32(stream)?;
            if i as usize >= deltas.len() {
                return Err("fixed delta index out of bounds".into());
            }
            s.push(i);
        }
        segments.push(s);
    }
    let count = read_uleb128_max4(stream)?;
    if count > super::MAX_TERMS_PER_LAYER {
        return Err("excessive fixed tokens".into());
    }
    let mut tokens = Vec::with_capacity(count);
    let mut expanded = 0usize;
    for _ in 0..count {
        let t = read_uleb128_max4_u32(stream)?;
        let s = segments
            .get(t as usize)
            .ok_or("fixed token out of bounds")?;
        expanded = expanded.saturating_add(s.len());
        if expanded > super::MAX_TERMS_PER_LAYER {
            return Err("fixed expansion budget exceeded".into());
        }
        tokens.push(t);
    }
    Ok(FixedStream {
        deltas,
        segments,
        tokens,
    })
}
