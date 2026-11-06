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

//! Projective binding and scalar extraction for the v2 prover.
//!
//! A table holds multilinear monomial coefficients, equivalently evaluations on
//! {0, infinity}^n. Binding one variable at z replaces each pair (a,b) by a + z*b.
//! Bit j of the array index is the exponent of variable x_j, with x_0 varying
//! fastest. Repeated low-variable bindings therefore evaluate the polynomial
//! at the challenges in their sampling order.
//! See Quang Dao, Ari Biswas, Liam Eagen, Andrew Milson, Shahar Papini, and Justin
//! Thaler, [*The Sum-Check Protocol over the Monomial Basis, and Other Optimizations*](https://eprint.iacr.org/2026/762), 2026.
use crate::runtime::algebra::RuntimeField;

/// Bind the low variable in place: v[i] = v[2i] + z*v[2i+1].
/// If P(x_0,...) = sum_i v[i] product_j x_j^i_j, the resulting array represents
/// P(z,x_1,...). For n input coefficients, its length is ceil(n/2), with the
/// remaining variables reindexed.
/// A missing odd coefficient is zero, so an unpaired entry or scalar is unchanged.
pub fn bind<const W: usize, F: RuntimeField<W>>(v: &mut Vec<F::E>, z: &F::E, f: &F) {
    assert!(!v.is_empty(), "cannot bind an empty vector");
    let pairs = v.len() / 2;
    for i in 0..pairs {
        let mut value = v[2 * i].clone();
        f.fma(&mut value, z, &v[2 * i + 1]);
        v[i] = value;
    }
    if v.len() % 2 != 0 {
        v[pairs] = v.last().expect("nonempty vector").clone();
    }
    v.truncate(v.len().div_ceil(2));
}

/// Extract the scalar remaining after all variables have been bound.
pub(super) fn as_scalar<const W: usize, F: RuntimeField<W>>(v: &[F::E]) -> F::E {
    assert_eq!(v.len(), 1, "vector length must be 1");
    v[0].clone()
}
