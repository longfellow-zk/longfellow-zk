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

use super::{Digest, MerkleProof};
use crate::core::algebra::SerializableField;

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
    pub(crate) fn sizes(&self) -> [usize; 5] {
        [self.nw, self.k, self.s, self.n, self.t]
    }
    pub(crate) fn validate(&self) -> Result<()> {
        let invalid = || Error::new(ErrorKind::InvalidInput, "invalid Polygero geometry");
        if self.sizes().iter().any(|&x| x > (1 << 28))
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
            .filter(|&x| x <= (1 << 28))
            .ok_or_else(invalid)?;
        Ok(())
    }
    pub(crate) fn data_rows(&self) -> usize {
        self.nw.div_ceil(self.row_width())
    }
    pub(crate) fn nrow(&self) -> usize {
        self.data_rows() + 3
    }
    pub(crate) fn response_lengths(&self) -> [usize; 2] {
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
    pub(crate) context: Digest,
    pub(crate) bodies: B,
    pub(crate) opening: MerkleProof,
}
impl<B> JointPolygeroProof<B> {
    /// Typed field bodies; no arithmetic is erased at the wire boundary.
    pub fn bodies(&self) -> &B {
        &self.bodies
    }
    /// Nonce bytes and frontier bytes, including the frontier length prefix.
    pub fn authentication_bytes(&self) -> (usize, usize) {
        (
            32 * self.opening.nonce.len(),
            4 + 32 * self.opening.path.len(),
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
    pub(crate) fn write<F: SerializableField<E = E>>(
        &self,
        out: &mut Vec<u8>,
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<()> {
        self.validate(g)?;
        for x in self.h.iter().chain(&self.z).chain(&self.rows) {
            super::util::write_elt_field(out, x, f);
        }
        Ok(())
    }
    pub(crate) fn read<F: SerializableField<E = E>>(
        bytes: &mut &[u8],
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<Self> {
        g.validate()?;
        let [h, z] = g.response_lengths();
        let rows = g.t * g.nrow();
        let size = (h + z + rows)
            .checked_mul(f.serialized_size_bytes())
            .ok_or_else(|| invalid("joint field size overflow"))?;
        if f.serialized_size_bytes() == 0 || bytes.len() < size {
            return Err(invalid("truncated joint field proof"));
        }
        let mut values = |n| {
            (0..n)
                .map(|_| read_field(bytes, f))
                .collect::<Result<Vec<_>>>()
        };
        Ok(Self {
            h: values(h)?,
            z: values(z)?,
            rows: values(rows)?,
        })
    }
}
fn invalid(message: &str) -> Error {
    Error::new(ErrorKind::InvalidData, message)
}
/// Reject aliases of the field's canonical encoding.
fn read_field<F: SerializableField>(bytes: &mut &[u8], field: &F) -> Result<F::E> {
    let width = field.serialized_size_bytes();
    let raw = bytes
        .get(..width)
        .ok_or_else(|| Error::new(ErrorKind::UnexpectedEof, "Polygero field element"))?;
    let value = field
        .bytes_to_element(raw)
        .map_err(|_| invalid("invalid field element"))?;
    if field.to_bytes(&value) != raw {
        return Err(invalid("noncanonical field element"));
    }
    *bytes = &bytes[width..];
    Ok(value)
}

/// Validate the shared authentication shape before reading or hashing columns.
pub(crate) fn validate_opening(p: &MerkleProof, t: usize, n: usize) -> Result<()> {
    if t == 0
        || t > n
        || n > (1 << 28)
        || p.nonce.len() != t
        || t.checked_mul(n.next_power_of_two().trailing_zeros() as usize + 1)
            .is_none_or(|max| p.path.len() > max)
    {
        return Err(invalid("joint opening shape"));
    }
    Ok(())
}
impl<B> JointPolygeroProof<B> {
    /// The field traversal supplies canonical bodies; the shared envelope owns
    /// the version, context and single Merkle opening for any participant count.
    pub(crate) fn write_to_buf<E: From<Error>>(
        &self,
        out: &mut Vec<u8>,
        context: &Digest,
        t: usize,
        n: usize,
        write_bodies: impl FnOnce(&B, &mut Vec<u8>) -> std::result::Result<(), E>,
    ) -> std::result::Result<(), E> {
        if self.context != *context {
            return Err(invalid("joint proof context mismatch").into());
        }
        validate_opening(&self.opening, t, n)?;
        out.extend_from_slice(b"JPG2");
        out.extend_from_slice(&context.data);
        write_bodies(&self.bodies, out)?;
        self.opening.write_nonces(out);
        self.opening.write_path(out);
        Ok(())
    }
    pub(crate) fn read<E: From<Error>>(
        bytes: &mut &[u8],
        context: &Digest,
        t: usize,
        n: usize,
        read_bodies: impl FnOnce(&mut &[u8]) -> std::result::Result<B, E>,
    ) -> std::result::Result<Self, E> {
        if t == 0 || t > n || n > (1 << 28) {
            return Err(invalid("joint opening geometry").into());
        }
        if bytes.get(..4) != Some(b"JPG2") || bytes.get(4..36) != Some(context.data.as_slice()) {
            return Err(invalid("joint proof version or context").into());
        }
        *bytes = &bytes[36..];
        let bodies = read_bodies(bytes)?;
        // Check all nonce bytes and the frontier length before allocation.
        let nonce_bytes = t
            .checked_mul(32)
            .and_then(|len| len.checked_add(4))
            .ok_or_else(|| invalid("joint opening size overflow"))?;
        if bytes.len() < nonce_bytes {
            return Err(invalid("truncated joint opening").into());
        }
        let nonce = MerkleProof::read_nonces(bytes, t)?;
        let count = u32::from_le_bytes(bytes[..4].try_into().unwrap()) as usize;
        if count > (bytes.len() - 4) / 32 {
            return Err(invalid("truncated joint frontier").into());
        }
        let path = MerkleProof::read_path(
            bytes,
            t,
            n.next_power_of_two().trailing_zeros() as usize + 1,
        )?;
        Ok(Self {
            context: *context,
            bodies,
            opening: MerkleProof { nonce, path },
        })
    }
}
