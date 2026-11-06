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

//! Batch v1 linear and product-copy constraints into logical row coefficients.
//!
//! Both roles form the same dense vector a: each sparse linear term contributes
//! alphal[c]*k to its original witness slot; each product-copy equality contributes
//! a positive weight at the copy and its negative at the original. The row helper
//! surrounds those coefficients with zero mask slots before interpolation.
use crate::runtime::{
    algebra::RuntimeField,
    v1::ligero::param::{LigeroLinearConstraint, LigeroParam, LigeroQuadraticConstraint},
};

/// Computes the linear combination coefficients vector `a` for the verifier's
/// inner product test.
///
/// The verifier combines the linear constraints (weighted by `alphal`) and the
/// quadratic triple consistency checks (weighted by `alphaq`) into a single
/// consolidated linear constraint over the tableau elements.
///
/// Specifically, for each linear constraint `c` with term `K_{c,w} * W_w`, the
/// coefficient of `W_w` accumulates `alphal[c] * K_{c,w}`.
///
/// For each quadratic constraint `iw` representing `W_{l.x} * W_{l.y} =
/// W_{l.z}`, virtual witness elements `X_iw`, `Y_iw`, `Z_iw` are placed in the
/// tableau. The consistency constraint ensures `X_iw = W_{l.x}`, `Y_iw = W_{l.
/// y}`, and `Z_iw = W_{l.z}`. The verifier checks this consistency using random
/// challenge coefficients `alphaq[iw] = (rx, ry, rz)`.
/// Thus:
/// - `X_iw` coefficient accumulates `rx`, while the corresponding `W_{l.x}` coefficient is reduced
///   by `rx`.
/// - `Y_iw` coefficient accumulates `ry`, while the corresponding `W_{l.y}` coefficient is reduced
///   by `ry`.
/// - `Z_iw` coefficient accumulates `rz`, while the corresponding `W_{l.z}` coefficient is reduced
///   by `rz`.
pub fn inner_product_vector<const W: usize, F: RuntimeField<W>>(
    param: &LigeroParam,
    llterm: &[LigeroLinearConstraint<W, F>],
    alphal: &[F::E],
    lqc: &[LigeroQuadraticConstraint],
    alphaq: &[[F::E; 3]],
    f: &F,
) -> Vec<F::E> {
    let mut a = vec![f.zero(); param.nwqrow * param.w];

    // 1. Accumulate coefficients from linear constraints: For each linear constraint term, add
    //    alphal[c] * term.k to the coefficient of W[term.w].
    for term in llterm {
        assert!(term.w < param.nw);
        assert!(term.c < alphal.len());
        f.fma(&mut a[term.w], &term.k, &alphal[term.c]);
    }

    let nqtriples_w = param.nqtriples * param.w;
    let ax_offset = param.nwrow * param.w;
    let ay_offset = ax_offset + nqtriples_w;
    let az_offset = ay_offset + nqtriples_w;

    // 2. Accumulate coefficients from quadratic consistency constraints: For each quadratic triple
    //    consistency check, add challenge coefficients to the virtual variables and subtract them
    //    from the actual witness variables.
    for i in 0..param.nqtriples {
        let mut j = 0;
        while j < param.w && j + i * param.w < param.nq {
            let iw = j + i * param.w;
            let l = &lqc[iw];
            assert!(l.x < param.nw, "l.x out of bounds: {} >= {}", l.x, param.nw);
            assert!(l.y < param.nw, "l.y out of bounds: {} >= {}", l.y, param.nw);
            assert!(l.z < param.nw, "l.z out of bounds: {} >= {}", l.z, param.nw);

            // X_iw consistency: rx * (X_iw - W_{l.x})
            f.add(&mut a[ax_offset + iw], &alphaq[iw][0]);
            f.sub(&mut a[l.x], &alphaq[iw][0]);

            // Y_iw consistency: ry * (Y_iw - W_{l.y})
            f.add(&mut a[ay_offset + iw], &alphaq[iw][1]);
            f.sub(&mut a[l.y], &alphaq[iw][1]);

            // Z_iw consistency: rz * (Z_iw - W_{l.z})
            f.add(&mut a[az_offset + iw], &alphaq[iw][2]);
            f.sub(&mut a[l.z], &alphaq[iw][2]);

            j += 1;
        }
    }
    a
}

/// Write logical samples for coefficient row i into an existing buffer. Mask
/// slots and any extension workspace are zero; witness slots receive row i of a.
pub fn layout_aext_into<const W: usize, F: RuntimeField<W>>(
    param: &LigeroParam,
    i: usize,
    a: &[F::E],
    a_ext: &mut [F::E],
    f: &F,
) {
    crate::runtime::algebra::blas::clear(a_ext, f);
    crate::runtime::algebra::blas::copy(
        &mut a_ext[param.r..param.r + param.w],
        &a[i * param.w..(i + 1) * param.w],
    );
}
