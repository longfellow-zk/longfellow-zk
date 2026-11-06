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

//! Interpolation capacity and sparse linear terms for a Polygero invocation.
//!
//! The caller selects k, s, n, t. `PolygeroParam` validates them against the
//! witness layout and interpolation backend. Linear terms describe A*w+b=0.

#[cfg(any(test, feature = "prover", feature = "verifier", feature = "compiler"))]
impl crate::runtime::proto::polygero::PolygeroConfig {
    /// Capacity for every interpolation used by the nonrecursive protocol.
    /// All ranges are contained in U = [0,k) || [k,k+n).
    pub fn can_interpolate<
        const W: usize,
        F: crate::runtime::algebra::RuntimeField<W>,
        D: crate::runtime::algebra::RangeInterpolatorFactory<W, F>,
    >(
        &self,
        domain: &D,
    ) -> bool {
        let Some(end) = self.k.checked_add(self.n) else {
            return false;
        };
        let Some(work) = self.k.checked_add(self.s) else {
            return false;
        };
        let Some(double) = self.k.checked_mul(2) else {
            return false;
        };
        if self.k == 0 || self.t >= self.k || work > self.n || double > self.n {
            return false;
        }
        let oracle = self.k..end;
        [
            (0..self.k, oracle.clone()), // Rows, m, selector z_R, and verifier C_i.
            (0..self.k + 1, oracle.clone()), // Public vanishing polynomial V.
            (0..self.k, self.k..self.k + double), // Prover C_i on Z's oracle points.
            (self.k..double, oracle.clone()), // Free arithmetic mask u.
            (self.k..self.k + work, oracle.clone()), // Primary mask and H verification.
            (self.k..self.k + self.s + 1, self.k..self.k + work), // B_i at H samples.
            (self.k..self.k + self.s + 1, oracle), // B_i at verifier columns.
            (self.k..self.k + double, 0..end), // Z for the global sum and column checks.
        ]
        .into_iter()
        .all(|(source, destination)| domain.can_interpolate(source, destination))
    }
}
/// One sparse term: add k*w[w] to equation c of A*w+b=0.
/// Repeated (c,w) entries contribute additively; b is supplied separately.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolygeroLinearTerm<E> {
    /// Equation index.
    pub c: usize,
    /// Witness index.
    pub w: usize,
    /// Field coefficient of this term.
    pub k: E,
}
