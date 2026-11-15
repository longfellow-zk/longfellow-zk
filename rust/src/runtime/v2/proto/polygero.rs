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

//! Public dimensions, witness coordinates, and the ambient-field Polygero wire format.
//!
//! Geometry determines the lengths of H, Z, packed rows and Merkle nonces.
//! Each row contains its t queried values in transcript order, with rows consecutive
//! in memory and on the wire. Every committed row is opened at those columns.
//! All responses and opened rows use canonical full-width field elements.
use std::io::{Error, ErrorKind, Result};

use super::{read_field, Digest, MerkleProof, NONCE_LEN};
use crate::core::algebra::SerializableField;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::v2::transcript::SEAL_BYTES;

/// Upper bound on every Polygero dimension and on the committed cell count.
const MAX_SIZE: usize = 1 << 28;

/// The most frontier digests one opened column contributes: one per tree level.
fn frontier_per_query(n: usize) -> usize {
    n.next_power_of_two().trailing_zeros() as usize + 1
}

/// Public dimensions of a nonrecursive invocation, selected by the caller.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolygeroConfig {
    /// Dimension of ordinary row polynomials.
    pub k: usize,
    /// Batching-polynomial degree bound; each B_i has s+1 samples.
    pub s: usize,
    /// Number of committed oracle columns.
    pub n: usize,
    /// Distinct opened columns and random prefix samples reserved in each row.
    pub t: usize,
}

/// Public counts used to validate proof shape and derive the committed row layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolygeroGeometry {
    pub(crate) nw: usize,
    pub(crate) k: usize,
    pub(crate) s: usize,
    pub(crate) n: usize,
    pub(crate) t: usize,
}
impl PolygeroGeometry {
    /// The geometry of `config` over `nw` witnesses, if it is valid.
    pub fn new(nw: usize, config: PolygeroConfig) -> Result<Self> {
        let PolygeroConfig { k, s, n, t } = config;
        let geom = Self { nw, k, s, n, t };
        geom.validate()?;
        Ok(geom)
    }
    /// The geometry of `config` over `nw` witnesses, which an enclosing
    /// proof geometry has already validated (proto I8).
    pub(super) fn validated(nw: usize, config: PolygeroConfig) -> Self {
        let PolygeroConfig { k, s, n, t } = config;
        let geom = Self { nw, k, s, n, t };
        debug_assert!(geom.validate().is_ok());
        geom
    }
    /// The profile `(k, s, n, t)` of this geometry.
    pub fn config(&self) -> PolygeroConfig {
        PolygeroConfig {
            k: self.k,
            s: self.s,
            n: self.n,
            t: self.t,
        }
    }
    pub(crate) fn sizes(&self) -> [usize; 5] {
        [self.nw, self.k, self.s, self.n, self.t]
    }
    /// Check the dimensions; the other counts assume a valid geometry.
    pub fn validate(&self) -> Result<()> {
        let invalid = || Error::new(ErrorKind::InvalidInput, "invalid Polygero geometry");
        if self.sizes().iter().any(|&x| x > MAX_SIZE)
            || self.k == 0
            || self.t >= self.k
            || self.t == 0
            || self.t > self.n
            || self.k.checked_add(self.s).is_none_or(|d| d > self.n)
            || self.k.checked_mul(2).is_none_or(|d| d > self.n)
        {
            return Err(invalid());
        }
        self.nrow()
            .checked_mul(self.n)
            .filter(|&x| x <= MAX_SIZE)
            .ok_or_else(invalid)?;
        Ok(())
    }
    pub(crate) fn data_rows(&self) -> usize {
        self.nw.div_ceil(self.row_width())
    }
    /// Committed rows of a valid geometry: the data rows and three further rows.
    pub fn nrow(&self) -> usize {
        self.data_rows() + 3
    }
    /// Lengths of the two response polynomials of a valid geometry.
    pub fn response_lengths(&self) -> [usize; 2] {
        [self.k + self.s, 2 * self.k]
    }

    /// Witness slots in an ordinary row, after its random prefix.
    pub(crate) fn row_width(&self) -> usize {
        self.k - self.t
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolygeroCommitment {
    pub(crate) root: Digest,
}
/// One typed participant's responses and queried rows, without authentication.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldProof<E> {
    /// H on the first k+s oracle nodes.
    pub(crate) h: Vec<E>,
    /// Z on the first 2k oracle nodes.
    pub(crate) z: Vec<E>,
    /// Rows u, m, witness, fstar; each holds t values in query order.
    pub(crate) rows: Vec<E>,
}
/// A recursive tuple of field bodies and a single shared column opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointPolygeroProof<B> {
    pub(crate) bodies: B,
    pub(in crate::runtime::v2) opening: MerkleProof,
}
impl<B> JointPolygeroProof<B> {
    /// Typed field bodies; no arithmetic is erased at the wire boundary.
    pub fn bodies(&self) -> &B {
        &self.bodies
    }
    /// Nonce bytes and frontier bytes, the frontier's u64 count included.
    pub fn authentication_bytes(&self) -> (usize, usize) {
        (
            NONCE_LEN * self.opening.nonce.len(),
            8 + 32 * self.opening.path.len(),
        )
    }
}
impl<E> FieldProof<E> {
    /// Canonical response and opened-row payload, excluding authentication.
    pub fn payload_bytes<F: SerializableField<E = E>>(&self, f: &F) -> usize {
        (self.h.len() + self.z.len() + self.rows.len()) * f.serialized_size_bytes()
    }
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
    /// The interactive response: H, then Z.
    pub(crate) fn write_response<F: SerializableField<E = E>>(
        &self,
        out: &mut Vec<u8>,
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<()> {
        self.validate(g)?;
        for x in self.h.iter().chain(&self.z) {
            super::util::write_elt_field(out, x, f);
        }
        Ok(())
    }
    /// The terminal rows u, m, witness, f*, t values each in query order.
    pub(crate) fn write_rows<F: SerializableField<E = E>>(
        &self,
        out: &mut Vec<u8>,
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<()> {
        self.validate(g)?;
        for x in &self.rows {
            super::util::write_elt_field(out, x, f);
        }
        Ok(())
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
    if t == 0
        || t > n
        || n > MAX_SIZE
        || p.nonce.len() != t
        || t.checked_mul(frontier_per_query(n))
            .is_none_or(|max| p.path.len() > max)
    {
        return Err(invalid("joint opening shape"));
    }
    Ok(())
}
/// Check a complete proof's length before decoding anything (proto I3):
/// `len = prefix + fixed + 8 + 32 f + 32`, where `fixed` covers every field
/// before the frontier and `f`, the u64 frontier count that follows them, is
/// at most `t (ceil(log2 n) + 1)`. Every truncation and every extension of a
/// proof fails here. Returns the body without the prefix and the seal block.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) fn checked_body(
    bytes: &[u8],
    prefix: usize,
    fixed: usize,
    t: usize,
    n: usize,
) -> Result<&[u8]> {
    if t == 0 || t > n || n > MAX_SIZE {
        return Err(invalid("joint opening geometry"));
    }
    let start = prefix
        .checked_add(fixed)
        .ok_or_else(|| invalid("proof length overflow"))?;
    let count = bytes
        .get(start..)
        .and_then(|rest| rest.first_chunk::<8>())
        .ok_or_else(|| invalid("proof length"))?;
    let cap = t
        .checked_mul(frontier_per_query(n))
        .ok_or_else(|| invalid("frontier capacity overflow"))?;
    let expected = usize::try_from(u64::from_le_bytes(*count))
        .ok()
        .filter(|&f| f <= cap)
        .and_then(|f| f.checked_mul(32))
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
    /// Write each field's response, then each field's rows, then the nonces,
    /// then the frontier (its count, then its digests): the last field of
    /// every body.
    pub(crate) fn write_to_buf<E: From<Error>>(
        &self,
        out: &mut Vec<u8>,
        t: usize,
        n: usize,
        write_responses: impl FnOnce(&B, &mut Vec<u8>) -> std::result::Result<(), E>,
        write_rows: impl FnOnce(&B, &mut Vec<u8>) -> std::result::Result<(), E>,
    ) -> std::result::Result<(), E> {
        validate_opening(&self.opening, t, n)?;
        write_responses(&self.bodies, out)?;
        write_rows(&self.bodies, out)?;
        self.opening.write_nonces(out);
        self.opening.write_path(out);
        Ok(())
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
        if t == 0 || t > n || n > MAX_SIZE {
            return Err(invalid("joint opening geometry").into());
        }
        let mut bodies = read_responses(bytes)?;
        read_rows(&mut bodies, bytes)?;
        let nonce = MerkleProof::read_nonces(bytes, t)?;
        let path = MerkleProof::read_path(bytes, t, frontier_per_query(n))?;
        if !bytes.is_empty() {
            return Err(invalid("bytes after the Merkle frontier").into());
        }
        Ok(Self {
            bodies,
            opening: MerkleProof { nonce, path },
        })
    }
}
