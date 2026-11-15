// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::fp24::Q,
    mldsa::{
        proto::{MlDsa44, MlDsa65},
        runtime::reference::ntt,
    },
    runtime::random::{DeterministicRng, RandomEngine},
};
fn dot(a: &[u32], b: &[u32]) -> u32 {
    a.iter().zip(b).fold(0, |v, (&x, &y)| add(v, mul(x, y)))
}
fn check<P: MlDsaParams>() {
    let mut rng = DeterministicRng::new(1928);
    let mut next = || (rng.u128() % u128::from(Q)) as u32;
    let x = std::array::from_fn(|_| next());
    let y = std::array::from_fn(|_| next());
    let mut nx = x;
    ntt(&mut nx);
    let mut ty = y;
    transpose_ntt(&mut ty);
    assert_eq!(dot(&nx, &y), dot(&x, &ty));
    let a: Vec<Vec<[u32; N]>> = (0..P::K)
        .map(|_| (0..P::L).map(|_| std::array::from_fn(|_| next())).collect())
        .collect();
    let t1: Vec<_> = (0..P::K).map(|_| std::array::from_fn(|_| next())).collect();
    let lambda: [Vec<[u32; N]>; CLAIMS] =
        std::array::from_fn(|_| (0..P::K).map(|_| std::array::from_fn(|_| next())).collect());
    let z: Vec<[u32; N]> = (0..P::L)
        .map(|_| std::array::from_fn(|_| next() & ((1 << P::Z_BITS) - 1)))
        .collect();
    let high: Vec<[u32; N]> = (0..P::K)
        .map(|_| std::array::from_fn(|_| next() & ((1 << P::R1_BITS) - 1)))
        .collect();
    let low: Vec<[u32; N]> = (0..P::K)
        .map(|_| std::array::from_fn(|_| next() & ((1 << P::r0_bits()) - 1)))
        .collect();
    let positive: [u32; N] = std::array::from_fn(|_| next() & 1);
    let negative: [u32; N] = std::array::from_fn(|_| next() & 1);
    let words: Vec<_> = z
        .iter()
        .flatten()
        .chain(high.iter().flatten())
        .chain(low.iter().flatten())
        .chain(&positive)
        .chain(&negative)
        .copied()
        .collect();
    let mut nz: Vec<_> = z
        .iter()
        .map(|row| row.map(|v| sub(v, P::GAMMA1 - P::REJECTION_BOUND - 1)))
        .collect();
    for row in &mut nz {
        ntt(row);
    }
    let mut nc = std::array::from_fn(|i| sub(positive[i], negative[i]));
    ntt(&mut nc);
    let mut nw: Vec<_> = (0..P::K)
        .map(|r| {
            std::array::from_fn(|i| sub(add(mul(2 * P::GAMMA2, high[r][i]), low[r][i]), P::GAMMA2))
        })
        .collect();
    for row in &mut nw {
        ntt(row);
    }
    let projected = project::<P>(&a, &t1, &lambda);
    assert_eq!(projected.weights.len(), words.len());
    for t in 0..CLAIMS {
        let mut expected = 0;
        for r in 0..P::K {
            for i in 0..N {
                let az = (0..P::L).fold(0, |v, j| add(v, mul(a[r][j][i], nz[j][i])));
                let residual = add(sub(nw[r][i], az), mul(t1[r][i], nc[i]));
                expected = add(expected, mul(lambda[t][r][i], residual));
            }
        }
        let actual = words
            .iter()
            .zip(&projected.weights)
            .fold(0, |sum, (&word, weight)| add(sum, mul(word, weight[t])));
        assert_eq!(
            sub(actual, projected.targets[t]),
            expected,
            "projection {t}"
        );
    }
}
#[test]
fn public_projection_matches_ntt_equations_44() {
    check::<MlDsa44>();
}
#[test]
fn public_projection_matches_ntt_equations_65() {
    check::<MlDsa65>();
}
