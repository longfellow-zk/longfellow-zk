// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
/// Verification needs one linear combination of each matrix row. Compute it
/// directly, so the full matrix need not be allocated or written to memory.
pub(in crate::runtime::v2::simd_sumcheck::adapter) fn verifier_weights(
    claim: &Claim,
    delta: &[E; 128],
    parameters: &Parameters,
    f: &F,
) -> Vec<E> {
    let gamma = delta.map(|x| f.mulf(&x, &x));
    let mut weights = vec![
        f.zero();
        claim
            .factors
            .iter()
            .map(|factor| factor.words.len())
            .max()
            .unwrap_or(0)
    ];
    for (word, row) in coordinate_rows(claim) {
        weights[word] = f.mulf(&parameters.dual()[127], &dot(&row, &gamma, f));
    }
    for factor in &claim.factors {
        if coordinate(&factor.lanes).is_some() {
            continue;
        }
        let images = std::array::from_fn(|h| {
            let row = factor.lanes.map(|v| f.mulf(&E::from(1u128 << h), &v));
            let numerators = dual_coordinate_numerators(&row);
            f.mulf(&parameters.dual()[127], &dot(&numerators, &gamma, f))
        });
        accumulate_map(&mut weights, &factor.words, &images, f);
    }
    weights
}
