// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Decode LFC3 directly into concrete v2 streams.
use std::io::BufRead;

use super::CircuitReader;
use crate::{
    core::proto::{
        uleb::{read_uleb128_max4, read_uleb128_max4_u32},
        v2::{self, Circuit, Constant, Layer, Linear, Quadratic, RawCircuit, Stream},
        SerializableField,
    },
    util::ceil_log2,
};

fn bounded<R: BufRead>(input: &mut R, max: usize, what: &str) -> Result<usize, String> {
    let n = read_uleb128_max4(input)?;
    if n > max {
        return Err(format!("LFC3 excessive {what}: {n} > {max}"));
    }
    Ok(n)
}
fn delta<R: BufRead>(input: &mut R) -> Result<u32, String> {
    let n = read_uleb128_max4_u32(input)?;
    Ok((n >> 1) ^ ((n & 1).wrapping_neg()))
}

// Only dictionary I/O and translated-run bounds checking are generic. Records
// retain their exact arity throughout decoding and numerical evaluation.
fn read_stream<R: BufRead, T, const N: usize>(
    input: &mut R,
    decode: impl Fn(&mut R) -> Result<T, String>,
    coordinates: impl Fn(&T) -> [u32; N],
    limits: [usize; N],
    remaining: &mut usize,
) -> Result<Stream<T>, String> {
    let n = bounded(input, super::MAX_DELTAS, "deltas")?;
    let mut deltas = Vec::with_capacity(n);
    for _ in 0..n {
        deltas.push(decode(input)?);
    }
    let n = bounded(input, super::MAX_DELTAS, "segments")?;
    let mut segments = Vec::with_capacity(n);
    let mut summaries = Vec::with_capacity(n);
    for _ in 0..n {
        let n = bounded(input, super::MAX_TERMS_PER_LAYER, "segment length")?;
        let mut segment = Vec::with_capacity(n);
        let (mut end, mut min, mut max) = ([0i64; N], [i64::MAX; N], [i64::MIN; N]);
        for _ in 0..n {
            let index = read_uleb128_max4_u32(input)?;
            let term = deltas
                .get(index as usize)
                .ok_or("LFC3 delta index out of bounds")?;
            for (j, d) in coordinates(term).into_iter().enumerate() {
                end[j] += i64::from(d as i32);
                min[j] = min[j].min(end[j]);
                max[j] = max[j].max(end[j]);
            }
            segment.push(index);
        }
        segments.push(segment);
        summaries.push((end, min, max));
    }
    let n = bounded(input, super::MAX_TERMS_PER_LAYER, "tokens")?;
    let mut tokens = Vec::with_capacity(n);
    let mut offset = [0i64; N];
    for _ in 0..n {
        let token = read_uleb128_max4_u32(input)?;
        let segment = segments
            .get(token as usize)
            .ok_or("LFC3 segment token out of bounds")?;
        *remaining = remaining
            .checked_sub(segment.len())
            .ok_or("LFC3 expanded term budget exceeded")?;
        if !segment.is_empty() {
            let (end, min, max) = summaries[token as usize];
            for j in 0..N {
                if offset[j] + min[j] < 0 || offset[j] + max[j] >= limits[j] as i64 {
                    return Err("LFC3 term coordinate out of bounds".into());
                }
                offset[j] += end[j];
            }
        }
        tokens.push(token);
    }
    Ok(Stream {
        deltas,
        segments,
        tokens,
    })
}

pub(super) fn from_stream<R: BufRead, F: SerializableField>(
    reader: &CircuitReader<'_, F>,
    input: &mut R,
    enforce_id: bool,
) -> Result<Circuit<F>, String> {
    let mut magic = [0; 4];
    input
        .read_exact(&mut magic)
        .map_err(|e| format!("LFC3 incomplete header: {e}"))?;
    if &magic != v2::encoding::MAGIC {
        return Err("expected LFC3 magic".into());
    }
    if read_uleb128_max4(input)? != reader.field_id as usize {
        return Err("LFC3 field ID mismatch".into());
    }
    let noutput = bounded(input, super::MAX_WIRES, "outputs")?;
    if read_uleb128_max4(input)? != 1 {
        return Err("LFC3 requires one circuit copy".into());
    }
    let npublic_input = bounded(input, super::MAX_WIRES, "public inputs")?;
    if read_uleb128_max4(input)? != 0 {
        return Err("LFC3 requires subfield_boundary = 0".into());
    }
    let ninput = bounded(input, super::MAX_WIRES, "inputs")?;
    if npublic_input > ninput {
        return Err("LFC3 public inputs exceed total inputs".into());
    }
    let nlayers = bounded(input, super::MAX_LAYERS, "layers")?;
    let nconstants = bounded(input, super::MAX_CONSTANTS - 3, "constants")?;
    let f = reader.f;

    let implicit = v2::implicit_constants(f)?;
    let mut bytes = vec![0; f.serialized_size_bytes()];
    let mut constants = Vec::with_capacity(nconstants + 3);
    constants.extend(implicit.iter().cloned());
    for _ in 0..nconstants {
        input
            .read_exact(&mut bytes)
            .map_err(|e| format!("LFC3 incomplete constant: {e}"))?;
        let k = f.bytes_to_element(&bytes)?;
        if implicit.contains(&k) {
            return Err("LFC3 implicit coefficient repeated in serialized table".into());
        }
        constants.push(k);
    }
    let coefficient = |input: &mut R| -> Result<u32, String> {
        let index = read_uleb128_max4_u32(input)?;
        if index == 2 && f.is_binary() {
            return Err("LFC3 binary terms must use coefficient index one for -1".into());
        }
        if index as usize >= constants.len() {
            return Err("LFC3 coefficient index out of bounds".into());
        }
        Ok(index)
    };
    let mut layers: Vec<Layer> = Vec::with_capacity(nlayers);
    let mut total_remaining = reader.max_total_terms;
    for _ in 0..nlayers {
        let logw = bounded(input, crate::core::proto::MAX_LOGW, "logw")?;
        let nw = bounded(input, super::MAX_LAYER_INPUTS, "layer inputs")?;
        if nw == 0 || logw != ceil_log2(nw) {
            return Err("LFC3 invalid layer width".into());
        }
        let outputs = layers.last().map_or(noutput, |layer| layer.nw);
        let budget = total_remaining.min(super::MAX_TERMS_PER_LAYER);
        let mut remaining = budget;
        let quadratic = read_stream(
            input,
            |input| {
                Ok(Quadratic {
                    g: delta(input)?,
                    l: delta(input)?,
                    r: delta(input)?,
                    k: coefficient(input)?,
                })
            },
            |term: &Quadratic| [term.g, term.l, term.r],
            [outputs, nw, nw],
            &mut remaining,
        )?;
        let linear = read_stream(
            input,
            |input| {
                Ok(Linear {
                    g: delta(input)?,
                    l: delta(input)?,
                    k: coefficient(input)?,
                })
            },
            |term: &Linear| [term.g, term.l],
            [outputs, nw],
            &mut remaining,
        )?;
        let constant = read_stream(
            input,
            |input| {
                Ok(Constant {
                    g: delta(input)?,
                    k: coefficient(input)?,
                })
            },
            |term: &Constant| [term.g],
            [outputs],
            &mut remaining,
        )?;
        if constant.deltas.iter().any(|t| t.k == 0) {
            return Err("LFC3 constant terms cannot have zero coefficients".into());
        }
        let layer = Layer::new(nw, quadratic, linear, constant);
        total_remaining -= budget - remaining;
        layers.push(layer);
    }
    if layers.last().map_or(noutput, |layer| layer.nw) != ninput {
        return Err("LFC3 input width mismatch".into());
    }
    let raw = RawCircuit {
        ninput,
        npublic_input,
        noutput,
        logv: ceil_log2(noutput),
        subfield_boundary: 0,
        constants,
        layers,
    };
    let mut id = [0; 32];
    input
        .read_exact(&mut id)
        .map_err(|e| format!("LFC3 incomplete circuit ID: {e}"))?;
    if enforce_id && v2::compute_id(f, &raw) != id {
        return Err("LFC3 circuit ID verification failed".into());
    }
    Ok(Circuit { raw, id })
}
