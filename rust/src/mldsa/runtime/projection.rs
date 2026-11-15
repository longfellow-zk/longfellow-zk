// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Public-key linear equations pulled back through the transposed NTT.
use crate::{
    mldsa::proto::{public_widths, MlDsaParams, CLAIMS, N, ZETAS},
    runtime::{
        algebra::fp24_ext6::{add_base as add, mul_base as mul, sub_base as sub},
        v2::foreign::adapter::exact::ExactClaims as Projections,
    },
};
#[cfg(test)]
mod tests;
/// Adjoint of the forward NTT, not the inverse NTT. Reverse the butterfly DAG.
pub(crate) fn transpose_ntt(a: &mut [u32; N]) {
    let mut k = N - 1;
    let mut len = 1;
    while len < N {
        for start in (0..N).step_by(2 * len).rev() {
            let zeta = ZETAS[k];
            k -= 1;
            for j in start..start + len {
                let u = a[j];
                let v = a[j + len];
                a[j] = add(u, v);
                a[j + len] = mul(zeta, sub(u, v));
            }
        }
        len *= 2;
    }
    assert_eq!(k, 0);
}

/// Six independent uniform row projections of F(w)-Ahat*F(z)+t1hat*F(c).
/// Public-key dependent coefficients are recomputed by the verifier.
pub(crate) fn project<P: MlDsaParams>(
    a_hat: &[Vec<[u32; N]>],
    t1hat: &[[u32; N]],
    lambda: &[Vec<[u32; N]>; CLAIMS],
) -> Projections {
    assert_eq!(a_hat.len(), P::K);
    assert_eq!(t1hat.len(), P::K);
    let mut weights = vec![[0; CLAIMS]; public_widths::<P>().len()];
    let mut targets = [0; CLAIMS];
    for t in 0..CLAIMS {
        assert_eq!(lambda[t].len(), P::K);
        let mut s = lambda[t].clone();
        for row in &mut s {
            transpose_ntt(row);
        }
        let mut z = vec![[0; N]; P::L];
        let mut c = [0; N];
        for row in 0..P::K {
            assert_eq!(a_hat[row].len(), P::L);
            for i in 0..N {
                for col in 0..P::L {
                    z[col][i] = sub(z[col][i], mul(lambda[t][row][i], a_hat[row][col][i]));
                }
                c[i] = add(c[i], mul(lambda[t][row][i], t1hat[row][i]));
            }
        }
        for row in &mut z {
            transpose_ntt(row);
        }
        transpose_ntt(&mut c);
        let sum = |v: &[[u32; N]]| v.iter().flatten().fold(0, |a, &b| add(a, b));
        targets[t] = add(
            mul(P::GAMMA2, sum(&s)),
            mul(P::GAMMA1 - P::REJECTION_BOUND - 1, sum(&z)),
        );
        let coefficients = z
            .into_iter()
            .flatten()
            .chain(s.iter().flatten().map(|&x| mul(2 * P::GAMMA2, x)))
            .chain(s.iter().flatten().copied())
            .chain(c)
            .chain(c.map(|x| sub(0, x)));
        for (weight, value) in weights.iter_mut().zip(coefficients) {
            weight[t] = value;
        }
    }
    Projections { weights, targets }
}
