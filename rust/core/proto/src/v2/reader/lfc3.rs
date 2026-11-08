// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Read and validate the complete allocation directory before the LFC3 payload.
use std::io::{BufRead, Read};

use super::CircuitReader;
use crate::{
    core::proto::{
        uleb::read_uleb128_max4_u32,
        v2::{
            self,
            directory::{self, LayerDirectory, StreamDirectory, REVISION},
            limits::*,
            uleb::read_size,
            Circuit, Constant, Layer, Linear, Quadratic, RawCircuit, Segments, Stream,
        },
        SerializableField,
    },
    util::ceil_log2,
};

fn bounded<R: BufRead>(input: &mut R, max: usize, what: &str) -> Result<usize, String> {
    let n = read_size(input)?;
    if n > max {
        return Err(format!("LFC3 excessive {what}: {n} > {max}"));
    }
    Ok(n)
}
fn delta<R: BufRead>(input: &mut R) -> Result<u32, String> {
    let n = read_uleb128_max4_u32(input)?;
    Ok((n >> 1) ^ ((n & 1).wrapping_neg()))
}
fn array<T>(n: usize) -> Result<Vec<T>, String> {
    let mut result = Vec::new();
    result
        .try_reserve_exact(n)
        .map_err(|e| format!("LFC3 allocation failed: {e}"))?;
    Ok(result)
}

fn read_stream<R: BufRead, T, const N: usize>(
    input: &mut R,
    d: StreamDirectory,
    ends: &[u32],
    decode: impl Fn(&mut std::io::Take<&mut R>) -> Result<T, String>,
    coordinates: impl Fn(&T) -> [u32; N],
    limits: [usize; N],
) -> Result<Stream<T>, String> {
    let mut payload = input.take(d.bytes as u64);
    let mut deltas = array(d.deltas)?;
    for _ in 0..d.deltas {
        deltas.push(decode(&mut payload)?);
    }
    let mut indices = array(d.indices)?;
    for _ in 0..d.indices {
        let index = read_uleb128_max4_u32(&mut payload)?;
        if index as usize >= deltas.len() {
            return Err("LFC3 delta index out of bounds".into());
        }
        indices.push(index);
    }
    let mut segment_ends = array(ends.len())?;
    segment_ends.extend_from_slice(ends);
    let segments = Segments::from_parts(segment_ends, indices)?;
    let mut summaries = array(d.segments)?;
    for segment in segments.iter() {
        let (mut end, mut min, mut max) = ([0i64; N], [i64::MAX; N], [i64::MIN; N]);
        for &index in segment {
            for (j, delta) in coordinates(&deltas[index as usize]).into_iter().enumerate() {
                end[j] += i64::from(delta as i32);
                min[j] = min[j].min(end[j]);
                max[j] = max[j].max(end[j]);
            }
        }
        summaries.push((end, min, max));
    }
    let mut tokens = array(d.tokens)?;
    let mut offset = [0i64; N];
    let mut terms = 0usize;
    for _ in 0..d.tokens {
        let token = read_uleb128_max4_u32(&mut payload)?;
        if token as usize >= segments.len() {
            return Err("LFC3 segment token out of bounds".into());
        }
        let segment = &segments[token as usize];
        terms = terms
            .checked_add(segment.len())
            .ok_or("LFC3 expanded term overflow")?;
        if terms > d.terms {
            return Err("LFC3 expanded term count mismatch".into());
        }
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
    if terms != d.terms || payload.limit() != 0 {
        return Err("LFC3 stream length mismatch".into());
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
    let mut header = [0; 8];
    input
        .read_exact(&mut header)
        .map_err(|e| format!("LFC3 incomplete header: {e}"))?;
    if &header[..4] != v2::encoding::MAGIC || &header[4..] != REVISION {
        return Err("expected LFC3 directory revision DIR1".into());
    }
    if read_size(input)? != reader.field_id as usize {
        return Err("LFC3 field ID mismatch".into());
    }
    let noutput = bounded(input, MAX_TOTAL_WIRES, "outputs")?;
    if noutput == 0 {
        return Err("LFC3 requires at least one output".into());
    }
    if read_size(input)? != 1 {
        return Err("LFC3 requires one circuit copy".into());
    }
    let npublic_input = bounded(input, MAX_TOTAL_WIRES, "public inputs")?;
    let ninput = bounded(input, MAX_TOTAL_WIRES, "inputs")?;
    if npublic_input > ninput {
        return Err("LFC3 public inputs exceed total inputs".into());
    }
    let nlayers = bounded(input, MAX_LAYERS, "layers")?;
    let nconstants = bounded(input, MAX_TOTAL_TERMS, "constants")?;
    let width = reader.f.serialized_size_bytes();
    if width == 0 || width > MAX_ARCHIVE_BYTES {
        return Err("LFC3 invalid field width".into());
    }
    let constants_bytes = nconstants
        .checked_mul(width)
        .ok_or("LFC3 constant size overflow")?;
    let mut directory = array(nlayers)?;
    for _ in 0..nlayers {
        let nw = bounded(input, MAX_TOTAL_WIRES, "layer inputs")?;
        let mut streams = [StreamDirectory::default(); 3];
        for stream in &mut streams {
            let mut counts = [0; 6];
            for n in &mut counts {
                *n = read_size(input)?;
            }
            *stream = StreamDirectory::from_counts(counts);
        }
        directory.push(LayerDirectory { nw, streams });
    }
    let totals = directory::validate(
        &directory,
        ninput,
        noutput,
        nconstants,
        constants_bytes,
        reader.max_total_terms,
    )?;
    let mut ends = array(totals[1])?;
    for layer in &directory {
        for stream in layer.streams {
            let mut previous = 0usize;
            for _ in 0..stream.segments {
                let length = bounded(input, stream.indices, "segment length")?;
                previous = previous
                    .checked_add(length)
                    .filter(|&end| end <= stream.indices)
                    .ok_or("LFC3 segment lengths exceed index count")?;
                ends.push(previous as u32);
            }
            if previous != stream.indices {
                return Err("LFC3 segment ends do not cover indices".into());
            }
        }
    }
    // All directory sizes, including aggregate dictionary storage and expanded
    // terms, have now passed validation. Payload arrays have exact capacities.
    let f = reader.f;
    let mut bytes = array(width)?;
    bytes.resize(width, 0);
    let mut constants = array(nconstants)?;
    for _ in 0..nconstants {
        input
            .read_exact(&mut bytes)
            .map_err(|e| format!("LFC3 incomplete constant: {e}"))?;
        let k = f.bytes_to_element(&bytes)?;
        if f.to_bytes(&k) != bytes {
            return Err("LFC3 noncanonical coefficient encoding".into());
        }
        constants.push(k);
    }
    let coefficient = |r: &mut std::io::Take<&mut R>| -> Result<u32, String> {
        let k = read_uleb128_max4_u32(r)?;
        if k as usize >= constants.len() {
            return Err("LFC3 coefficient index out of bounds".into());
        }
        Ok(k)
    };
    let classes = v2::classify_constants(f, &constants);
    let mut layers: Vec<Layer> = array(nlayers)?;
    let mut next_end = 0;
    for layer in directory {
        let outputs = layers.last().map_or(noutput, |l| l.nw);
        let [q, l, c] = layer.streams;
        let qends = &ends[next_end..next_end + q.segments];
        next_end += q.segments;
        let lends = &ends[next_end..next_end + l.segments];
        next_end += l.segments;
        let cends = &ends[next_end..next_end + c.segments];
        next_end += c.segments;
        let quadratic = read_stream(
            input,
            q,
            qends,
            |r| {
                Ok(Quadratic {
                    g: delta(r)?,
                    l: delta(r)?,
                    r: delta(r)?,
                    k: coefficient(r)?,
                })
            },
            |t| [t.g, t.l, t.r],
            [outputs, layer.nw, layer.nw],
        )?;
        let linear = read_stream(
            input,
            l,
            lends,
            |r| {
                Ok(Linear {
                    g: delta(r)?,
                    l: delta(r)?,
                    k: coefficient(r)?,
                })
            },
            |t| [t.g, t.l],
            [outputs, layer.nw],
        )?;
        let constant = read_stream(
            input,
            c,
            cends,
            |r| {
                Ok(Constant {
                    g: delta(r)?,
                    k: coefficient(r)?,
                })
            },
            |t| [t.g],
            [outputs],
        )?;
        if constant
            .deltas
            .iter()
            .any(|t| classes[t.k as usize] == v2::CoefficientClass::Zero)
        {
            return Err("LFC3 constant terms cannot have zero coefficients".into());
        }
        layers.push(Layer::with_assertions(
            layer.nw,
            quadratic,
            linear,
            constant,
            |k| classes[k as usize] == v2::CoefficientClass::Zero,
        ));
    }
    let raw = RawCircuit {
        ninput,
        npublic_input,
        noutput,
        logv: ceil_log2(noutput),
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
