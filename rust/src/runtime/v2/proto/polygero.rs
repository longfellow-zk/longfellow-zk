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

use super::{merkle::DIGEST_LEN, Digest, MerkleProof, NONCE_LEN};
use crate::core::algebra::SerializableField;

cfg_role! {
    pub(crate) mod codec;
}
cfg_prover! {
    mod prover;
}

/// Upper bound on every Polygero dimension and on the committed cell count.
const MAX_SIZE: usize = 1 << 28;

/// The most frontier digests one opened column contributes: one per tree level.
fn frontier_per_query(n: usize) -> usize {
    n.next_power_of_two().trailing_zeros() as usize + 1
}

/// Upper bound on a proof's Merkle frontier count, the formal model's cap
/// (Lean `OpeningBody.frontierCapacity`). Every valid geometry stays far below
/// it: it has at least three rows of `n` columns within `MAX_SIZE` cells, so
/// `t < k <= n / 2 < 2^26`, and a column contributes at most 28 digests.
/// `validate` and the opening checks enforce the cap all the same.
const MAX_FRONTIER: usize = u32::MAX as usize;

/// The frontier capacity `t (ceil(log2 n) + 1)` of an opening of `t` of `n`
/// columns, if the opening's shape is valid: `0 < t <= n <= MAX_SIZE`, with
/// a capacity of at most `MAX_FRONTIER`. This is the one opening-shape
/// check: geometry validation, the proof-length check, the reader and
/// `validate_opening` all use it.
fn opening_capacity(t: usize, n: usize) -> Option<usize> {
    if t == 0 || t > n || n > MAX_SIZE {
        return None;
    }
    t.checked_mul(frontier_per_query(n))
        .filter(|&cap| cap <= MAX_FRONTIER)
}

/// Public dimensions of a nonrecursive invocation, selected by the caller:
/// the one profile type of every application and tool. Profiles order
/// lexicographically by `(k, s, n, t)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
            || self.k.checked_add(self.s).is_none_or(|d| d > self.n)
            || self.k.checked_mul(2).is_none_or(|d| d > self.n)
            || opening_capacity(self.t, self.n).is_none()
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
            8 + DIGEST_LEN * self.opening.path.len(),
        )
    }
}
impl<E> FieldProof<E> {
    /// Canonical response and opened-row payload, excluding authentication.
    pub fn payload_bytes<F: SerializableField<E = E>>(&self, f: &F) -> usize {
        (self.h.len() + self.z.len() + self.rows.len()) * f.serialized_size_bytes()
    }
}
