// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The checks and the decoding of the Polygero wire format, which every proof
//! role runs; the encoding is the prover's (`prover.rs`).
use std::io::{Error, ErrorKind, Result};

use super::{
    super::read_field, opening_capacity, FieldProof, JointPolygeroProof, MerkleProof,
    PolygeroGeometry, DIGEST_LEN, NONCE_LEN,
};
use crate::{core::algebra::SerializableField, runtime::v2::transcript::SEAL_BYTES};

impl<E> FieldProof<E> {
    pub(crate) fn validate(&self, g: &PolygeroGeometry) -> Result<()> {
        g.validate()?;
        if [self.h.len(), self.z.len()] != g.response_lengths() || self.rows.len() != g.t * g.nrow()
        {
            return Err(invalid("joint field proof shape"));
        }
        Ok(())
    }
    /// Bytes of the interactive response (H, then Z) and of the terminal
    /// rows of a valid geometry; None if they overflow.
    pub(crate) fn wire_lengths(g: &PolygeroGeometry, width: usize) -> Option<[usize; 2]> {
        let [h, z] = g.response_lengths();
        Some([
            h.checked_add(z)?.checked_mul(width)?,
            g.t.checked_mul(g.nrow())?.checked_mul(width)?,
        ])
    }
    /// Read the response; the rows follow later (`read_rows`). The caller
    /// has checked the total length.
    pub(crate) fn read_response<F: SerializableField<E = E>>(
        bytes: &mut &[u8],
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<Self> {
        g.validate()?;
        let [h, z] = g.response_lengths();
        Ok(Self {
            h: read_values(bytes, h, f)?,
            z: read_values(bytes, z, f)?,
            rows: Vec::new(),
        })
    }
    pub(crate) fn read_rows<F: SerializableField<E = E>>(
        &mut self,
        bytes: &mut &[u8],
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<()> {
        self.rows = read_values(bytes, g.t * g.nrow(), f)?;
        Ok(())
    }
}
/// `n` canonical elements; the length is checked before allocating.
fn read_values<F: SerializableField>(bytes: &mut &[u8], n: usize, f: &F) -> Result<Vec<F::E>> {
    let size = n
        .checked_mul(f.serialized_size_bytes())
        .ok_or_else(|| invalid("joint field size overflow"))?;
    if f.serialized_size_bytes() == 0 || bytes.len() < size {
        return Err(invalid("truncated joint field proof"));
    }
    (0..n).map(|_| read_field(bytes, f)).collect()
}
fn invalid(message: &str) -> Error {
    Error::new(ErrorKind::InvalidData, message)
}
/// Validate the shared authentication shape before reading or hashing columns.
pub(in crate::runtime::v2) fn validate_opening(p: &MerkleProof, t: usize, n: usize) -> Result<()> {
    if p.nonce.len() != t || opening_capacity(t, n).is_none_or(|max| p.path.len() > max) {
        return Err(invalid("joint opening shape"));
    }
    Ok(())
}
/// Check a complete proof's length before decoding anything (proto I3):
/// `len = prefix + fixed + 8 + 32 f + 32`, where `fixed` covers every field
/// before the frontier and `f`, the u64 frontier count that follows them, is
/// at most `t (ceil(log2 n) + 1)`. Every truncation and every extension of a
/// proof fails here. Returns the body without the prefix and the seal block.
pub(crate) fn checked_body(
    bytes: &[u8],
    prefix: usize,
    fixed: usize,
    t: usize,
    n: usize,
) -> Result<&[u8]> {
    let cap = opening_capacity(t, n).ok_or_else(|| invalid("joint opening geometry"))?;
    let start = prefix
        .checked_add(fixed)
        .ok_or_else(|| invalid("proof length overflow"))?;
    let count = bytes
        .get(start..)
        .and_then(|rest| rest.first_chunk::<8>())
        .ok_or_else(|| invalid("proof length"))?;
    let expected = usize::try_from(u64::from_le_bytes(*count))
        .ok()
        .filter(|&f| f <= cap)
        .and_then(|f| f.checked_mul(DIGEST_LEN))
        .and_then(|x| x.checked_add(8 + SEAL_BYTES))
        .and_then(|x| x.checked_add(start))
        .ok_or_else(|| invalid("Merkle frontier count"))?;
    if bytes.len() != expected {
        return Err(invalid("proof length"));
    }
    Ok(&bytes[prefix..bytes.len() - SEAL_BYTES])
}
impl<B> JointPolygeroProof<B> {
    /// Bytes of the opening before its frontier: one nonce per column.
    pub(crate) fn fixed_opening_len(t: usize) -> Option<usize> {
        t.checked_mul(NONCE_LEN)
    }
    /// Read the counterpart of `write_to_buf` from the rest of a body whose
    /// total length the caller checked; nothing may follow the frontier.
    pub(crate) fn read<E: From<Error>>(
        bytes: &mut &[u8],
        t: usize,
        n: usize,
        read_responses: impl FnOnce(&mut &[u8]) -> std::result::Result<B, E>,
        read_rows: impl FnOnce(&mut B, &mut &[u8]) -> std::result::Result<(), E>,
    ) -> std::result::Result<Self, E> {
        let cap = opening_capacity(t, n).ok_or_else(|| invalid("joint opening geometry"))?;
        let mut bodies = read_responses(bytes)?;
        read_rows(&mut bodies, bytes)?;
        let nonce = MerkleProof::read_nonces(bytes, t)?;
        let path = MerkleProof::read_path(bytes, cap)?;
        if !bytes.is_empty() {
            return Err(invalid("bytes after the Merkle frontier").into());
        }
        Ok(Self {
            bodies,
            opening: MerkleProof { nonce, path },
        })
    }
}
