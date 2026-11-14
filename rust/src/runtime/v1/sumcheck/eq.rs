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

//! Boolean equality weights for the two v1 witness claims.
//!
//! For a Boolean index i, eq(g,i) is the product over bits of g[j] when i_j=1
//! and 1-g[j] otherwise. `eq2` expands eq(g0,i)+alpha*eq(g1,i) for every live
//! wire. `eval` computes the bounded contraction sum_{i<n} eq(a,i)*eq(b,i)
//! using two scalars rather than constructing either dense weight vector.
use crate::runtime::algebra::RuntimeField;

/// Bind both indices of the equality tensor restricted to the first n wires.
/// After each pair of coordinates, the remaining equal-index entries have
/// one common weight a and a possibly different final weight b. Binding the
/// next two bits leaves ceil(n/2) entries with the same form.
///
/// Let `i1j1=input_i`[0]*`input_j`[0] and i0j0=(1-input_i[0])*(1-input_j[0]).
///
/// A complete pair contributes a*(i0j0+i1j1).
///
/// For even n, the last pair has weights a,b, giving b <- a*i0j0+b*i1j1.
///
/// For odd n, its missing partner is zero, giving b <- b*i0j0.
pub fn eval<const W: usize, F: RuntimeField<W>>(
    logn: usize,
    mut n: usize,
    input_i: &[F::E],
    input_j: &[F::E],
    f: &F,
) -> F::E {
    assert!(input_i.len() >= logn && input_j.len() >= logn);
    let mut a = f.one();
    let mut b = f.one();
    for (i1, j1) in input_i[..logn].iter().zip(input_j[..logn].iter()) {
        let i0 = f.subf(&f.one(), i1);
        let j0 = f.subf(&f.one(), j1);
        let i0j0 = f.mulf(&i0, &j0);
        let i1j1 = f.mulf(i1, j1);
        if (n & 1) == 0 {
            f.mul(&mut b, &i1j1);
            f.fma(&mut b, &a, &i0j0);
        } else {
            f.mul(&mut b, &i0j0);
        }
        f.mul(&mut a, &f.addf(&i0j0, &i1j1));
        n = n.div_ceil(2);
    }
    b
}

/// Optimization for a special case: return a raw vector
///   eq[i] = EQ(G0, i) + alpha * EQ(G1, i)
/// for all 0 <= i < n.
pub fn eq2<const W: usize, F: RuntimeField<W>>(
    logn: usize,
    n: usize,
    g0: &[F::E],
    g1: &[F::E],
    alpha: &F::E,
    f: &F,
) -> Vec<F::E> {
    let mut eq = vec![f.zero(); n];
    fill_recursive(&mut eq, logn, n, g0, g1, &f.one(), alpha, f);
    eq
}

/// `fill_recursive(eq`, l, n, G0, G1, w0, w1, f) populates eq[0..n) with
///   eq[i] = w0 * EQ[G0, i] + w1 * EQ[G1, i]
#[allow(clippy::too_many_arguments)]
fn fill_recursive<const W: usize, F: RuntimeField<W>>(
    eq: &mut [F::E],
    l: usize,
    n: usize,
    g0: &[F::E],
    g1: &[F::E],
    w0: &F::E,
    w1: &F::E,
    f: &F,
) {
    assert!(eq.len() >= n && g0.len() >= l && g1.len() >= l && (l == 0 || !eq.is_empty()));
    if l > 0 {
        let nl = l - 1;
        let s = 1 << nl;

        let w0hi = f.mulf(w0, &g0[nl]);
        let w1hi = f.mulf(w1, &g1[nl]);
        let w0lo = f.subf(w0, &w0hi);
        let w1lo = f.subf(w1, &w1hi);
        if s < n {
            let (eq_lo, eq_hi) = eq[0..n].split_at_mut(s);
            fill_recursive(eq_lo, nl, s, g0, g1, &w0lo, &w1lo, f);
            fill_recursive(eq_hi, nl, n - s, g0, g1, &w0hi, &w1hi, f);
        } else {
            fill_recursive(&mut eq[0..n], nl, n, g0, g1, &w0lo, &w1lo, f);
        }
    } else {
        eq[0] = f.addf(w0, w1);
    }
}
