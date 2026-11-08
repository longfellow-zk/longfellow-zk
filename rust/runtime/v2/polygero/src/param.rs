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

//! Validate the public layout and bind the context used for commitment.
//!
//! `PolygeroConfig` supplies k, s, n, t; the witness count completes
//! the proof geometry. Construction checks dimensions and all
//! required interpolation shapes. It binds these values and the ordered domain
//! into the context used by transcript and Merkle hashing. The source-statement
//! digest is supplied later, directly to proving and verification.
//!
//! Row accessors define the common ordering of W: u, m, data rows, then fstar.
//! Polynomial samples and interpolation plans are computed by their consumers.
use super::{ensure, PolygeroConfig, PolygeroError, PolygeroGeometry};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{EvaluationDomain, RuntimeField},
        v2::proto::Digest,
    },
};

/// Validated public dimensions and transcript identity for one invocation.
#[derive(Clone, Debug)]
pub struct PolygeroParam {
    pub(super) geom: PolygeroGeometry,
    pub(super) domain_id: Vec<u8>,
    pub(super) context: Digest,
}
impl PolygeroParam {
    /// Validate dimensions and backend capacity; bind the public context.
    /// The statement derived later is supplied separately to prove/verify.
    /// This validates operational geometry, not a security target. Applications
    /// select certified parameters separately; small test configurations are valid here.
    /// Participants obtain their arithmetic field from the same domain, so a
    /// runtime-configured modulus cannot differ from the interpolation field.
    pub fn try_new<
        const W: usize,
        F: RuntimeField<W> + SerializableField,
        D: EvaluationDomain<W, F>,
    >(
        nw: usize,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, PolygeroError> {
        let PolygeroConfig { k, s, n, t } = config;
        let geom = PolygeroGeometry { nw, k, s, n, t };
        geom.validate()?;
        ensure(
            config.can_interpolate(domain),
            "interpolation capacity exceeded",
        )?;
        // Distinct points within admitted ranges are guaranteed by the backend.
        let id = domain.domain_id();
        let context = super::transcript::context_digest(&geom, &id);
        Ok(Self {
            geom,
            domain_id: id,
            context,
        })
    }
    /// The committed oracle is disjoint from the logical witness prefix.
    pub(super) fn oracle_range(&self) -> std::ops::Range<usize> {
        self.geom.k..self.geom.k + self.geom.n
    }
    /// Free masks, challenges and both responses start at the oracle's first point.
    pub(super) fn oracle_prefix(&self, length: usize) -> std::ops::Range<usize> {
        self.geom.k..self.geom.k + length
    }
    /// Dimensions and row layout needed to encode or decode a proof.
    pub fn geometry(&self) -> PolygeroGeometry {
        self.geom
    }
    /// The primary mask follows all rows that receive batching polynomials.
    pub(super) fn fstar_row(&self) -> usize {
        self.geom.nrow() - 1
    }

    pub(super) fn u_row(&self) -> usize {
        0
    }

    pub(super) fn m_row(&self) -> usize {
        1
    }

    /// Witness rows follow the two arithmetic masks.
    pub(super) fn data_start(&self) -> usize {
        2
    }

    /// Every row except fstar receives a challenge polynomial B_i in H.
    pub(super) fn batched_rows(&self) -> std::ops::Range<usize> {
        0..self.fstar_row()
    }
}
