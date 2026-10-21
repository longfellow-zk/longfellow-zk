// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

use runtime_algebra::RuntimeField;

/// Bind the low variable in place: v[i] = (1-r) v[2i] + r v[2i+1].
/// A missing final entry is zero; a scalar is multiplied by (1-r).
pub fn bind<const W: usize, F: RuntimeField<W>>(v: &mut Vec<F::E>, r: &F::E, f: &F) {
    assert!(!v.is_empty(), "cannot bind an empty vector");
    let pairs = v.len() / 2;
    for i in 0..pairs {
        let difference = f.subf(&v[2 * i + 1], &v[2 * i]);
        let mut value = v[2 * i].clone();
        f.fma(&mut value, &difference, r);
        v[i] = value;
    }
    if v.len() % 2 != 0 {
        v[pairs] = f.subf(&v[v.len() - 1], &f.mulf(r, &v[v.len() - 1]));
    }
    v.truncate(v.len().div_ceil(2));
}

/// Extract the endpoint after all variables have been bound.
pub fn as_scalar<const W: usize, F: RuntimeField<W>>(v: &[F::E]) -> F::E {
    assert_eq!(v.len(), 1, "vector length must be 1");
    v[0].clone()
}
