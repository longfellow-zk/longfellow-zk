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

//! The two public polynomials that attach masks to the arithmetic response Z.
//!
//! V(x) = product_{0 <= j < k}(x-x_j) vanishes on every logical point. Thus V*u
//! hides Z away from those points without altering its logical sum. The selector
//! z_R is zero on logical mask slots 0..t and one on witness slots t..k. Since m
//! has zero sum on the latter slots, z_R*m preserves the same sum while hiding
//! the individual constraint contributions.
//!
//! Both functions return oracle evaluations using the general interpolation
//! API. The verifier uses these same functions and gathers its queried columns.
use super::PolygeroGeometry;
use crate::runtime::algebra::{
    range_interpolation::interpolate_range, RangeInterpolatorFactory, RuntimeField,
};

/// Evaluate V, the monic polynomial vanishing on all K logical points, on the oracle.
pub(super) fn vanishing<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    geom: &PolygeroGeometry,
    domain: &D,
    f: &F,
) -> Vec<F::E> {
    let mut samples = vec![f.zero(); geom.k + 1];
    // K roots and one extra sample fix the monic polynomial of degree K.
    let x = domain.point(geom.k);
    let mut scale = f.one();
    // Each factor x - x_i vanishes at its logical point and has leading
    // coefficient +1; their product is the required monic normalization.
    for i in 0..geom.k {
        f.mul(&mut scale, &f.subf(&x, &domain.point(i)));
    }
    samples[geom.k] = scale;
    interpolate_range(0, &samples, geom.k..geom.k + geom.n, domain)
}

/// Evaluate z_R, zero on logical mask slots and one on witness slots, on the oracle.
pub(super) fn selector<const W: usize, F: RuntimeField<W>, D: RangeInterpolatorFactory<W, F>>(
    geom: &PolygeroGeometry,
    domain: &D,
    f: &F,
) -> Vec<F::E> {
    let mut selector = vec![f.one(); geom.k];
    selector[..geom.t].fill(f.zero());
    interpolate_range(0, &selector, geom.k..geom.k + geom.n, domain)
}
