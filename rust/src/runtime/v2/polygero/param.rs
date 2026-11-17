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

//! Validate the public layout of one Polygero invocation.
//!
//! `PolygeroConfig` supplies k, s, n, t; the witness count completes
//! the proof geometry. Construction checks dimensions and all
//! required interpolation shapes. Nothing here is hashed: the transcript
//! statement binds the profile and the cell counts, and the evaluation
//! domain's ID is bound nowhere, since the verifier fixes the domain.
//!
//! Row accessors define the common ordering of W: u, m, data rows, then fstar.
//! Polynomial samples and interpolation plans are computed by their consumers.
use super::{ensure, PolygeroError};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{range_interpolation::EvaluationDomain, RuntimeField},
        v2::proto::polygero::{PolygeroConfig, PolygeroGeometry},
    },
};

/// Validated public dimensions for one invocation, and the ID of the
/// evaluation domain they were validated against.
#[derive(Clone, Debug)]
#[cfg_attr(not(feature = "testonly"), allow(unreachable_pub))]
pub struct PolygeroParam {
    pub(super) geom: PolygeroGeometry,
    pub(super) domain_id: Vec<u8>,
}
impl PolygeroParam {
    /// Validate dimensions and backend capacity.
    /// The statement derived later is supplied separately to prove/verify.
    /// This validates operational geometry, not a security target. Applications
    /// select certified parameters separately; small test configurations are valid here.
    /// Participants obtain their arithmetic field from the same domain, so a
    /// runtime-configured modulus cannot differ from the interpolation field.
    #[cfg_attr(not(feature = "testonly"), allow(unreachable_pub))]
    pub fn try_new<F: RuntimeField + SerializableField, D: EvaluationDomain<F>>(
        nw: usize,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, PolygeroError> {
        let geom = PolygeroGeometry::new(nw, config)?;
        ensure(
            config.can_interpolate(domain),
            "interpolation capacity exceeded",
        )?;
        // Distinct points within admitted ranges are guaranteed by the backend.
        Ok(Self {
            geom,
            domain_id: domain.domain_id(),
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
    #[cfg_attr(not(feature = "testonly"), allow(unreachable_pub))]
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
