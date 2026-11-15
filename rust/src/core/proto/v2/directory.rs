// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! LFC3 directory records, shared by its reader and writer. Counts precede all
//! segment lengths; those lengths precede all constants, deltas, indices and tokens.
use super::limits::*;

pub(super) const REVISION: &[u8; 4] = b"DIR3";

#[derive(Clone, Copy, Default)]
pub(super) struct StreamDirectory {
    pub deltas: usize,
    pub segments: usize,
    pub indices: usize,
    pub tokens: usize,
    pub terms: usize,
    pub bytes: usize,
}
impl StreamDirectory {
    pub(super) fn counts(self) -> [usize; 6] {
        [
            self.deltas,
            self.segments,
            self.indices,
            self.tokens,
            self.terms,
            self.bytes,
        ]
    }
    pub(super) fn from_counts(
        [deltas, segments, indices, tokens, terms, bytes]: [usize; 6],
    ) -> Self {
        Self {
            deltas,
            segments,
            indices,
            tokens,
            terms,
            bytes,
        }
    }
    fn validate(self, arity: usize) -> Result<(), String> {
        let entries = self
            .deltas
            .checked_mul(arity)
            .and_then(|n| n.checked_add(self.indices))
            .and_then(|n| n.checked_add(self.tokens))
            .ok_or("LFC3 stream size overflow")?;
        // Every stored integer uses one to four ULEB bytes. This also prevents
        // a directory from declaring nonempty arrays with an empty payload.
        if self.bytes < entries
            || self.bytes > entries.checked_mul(4).ok_or("LFC3 stream size overflow")?
        {
            return Err("LFC3 invalid stream byte length".into());
        }
        Ok(())
    }
}
pub(super) struct LayerDirectory {
    pub nw: usize,
    pub streams: [StreamDirectory; 3],
}

/// Metadata charges against `MAX_METADATA_BYTES`. They are fixed, so a
/// circuit is accepted or rejected alike on every target; each is the
/// in-memory size on 64-bit targets, which no target exceeds (`directory`
/// tests). A segment is charged the worst (quadratic) summary, even though
/// only one stream's summaries are live at a time: directory and final
/// segment ends (2 x u32), nine i64 summary words and an assertion count
/// (a usize). A token is one u32. A layer is its directory and `Layer` records.
pub(super) const SEGMENT_METADATA_BYTES: usize = 88;
pub(super) const TOKEN_METADATA_BYTES: usize = 4;
pub(super) const LAYER_METADATA_BYTES: usize = 456;

/// Check the complete allocation plan before reading segment ends or payloads.
/// These are declared sizes, not counters maintained during circuit execution.
pub(super) fn validate(
    layers: &[LayerDirectory],
    ninput: usize,
    noutput: usize,
    nconstants: usize,
    constants_bytes: usize,
    limits: SizeLimits,
) -> Result<[usize; 6], String> {
    let mut total = [0usize; 6];
    let mut wires = noutput;
    for layer in layers {
        if layer.nw == 0 || layer.nw > limits.total_wires {
            return Err("LFC3 invalid layer width".into());
        }
        wires = wires
            .checked_add(layer.nw)
            .ok_or("LFC3 wire count overflow")?;
        for (stream, arity) in layer.streams.iter().zip([4, 3, 2]) {
            stream.validate(arity)?;
            for (sum, n) in total.iter_mut().zip(stream.counts()) {
                *sum = sum.checked_add(n).ok_or("LFC3 directory count overflow")?;
            }
        }
    }
    if layers.last().map_or(noutput, |l| l.nw) != ninput {
        return Err("LFC3 input width mismatch".into());
    }
    total[5] = total[5]
        .checked_add(constants_bytes)
        .ok_or("LFC3 payload size overflow")?;
    if wires > limits.total_wires {
        return Err("LFC3 excessive total wires".into());
    }
    let stored = total[0]
        .checked_add(total[2])
        .and_then(|n| n.checked_add(nconstants))
        .ok_or("LFC3 stored term count overflow")?;
    if stored > limits.stored_terms || total[4] > limits.expanded_terms {
        return Err("LFC3 excessive total terms".into());
    }
    let metadata = total[1]
        .checked_mul(SEGMENT_METADATA_BYTES)
        .and_then(|n| {
            total[3]
                .checked_mul(TOKEN_METADATA_BYTES)
                .and_then(|m| n.checked_add(m))
        })
        .and_then(|n| {
            layers
                .len()
                .checked_mul(LAYER_METADATA_BYTES)
                .and_then(|m| n.checked_add(m))
        })
        .ok_or("LFC3 metadata size overflow")?;
    if metadata > limits.metadata_bytes {
        return Err("LFC3 excessive segment/token metadata".into());
    }
    if total[5] > MAX_ARCHIVE_BYTES {
        return Err("LFC3 excessive payload size".into());
    }
    Ok(total)
}

#[cfg(test)]
mod tests;
