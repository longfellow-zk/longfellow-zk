// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Factored trace pairing; coordinate factors use a sparse block transpose.
use super::{Claim, Parameters, E, F};
use crate::{
    core::algebra::AlgebraicField,
    runtime::algebra::{blas::dot, packing::binary128::dual_coordinate_numerators},
};
fn coordinate(lanes: &[E; 128]) -> Option<usize> {
    let mut nonzero = lanes.iter().enumerate().filter(|(_, x)| **x != E::from(0));
    let (j, x) = nonzero.next()?;
    (*x == E::from(1) && nonzero.next().is_none()).then_some(j)
}
/// Coalesce coordinate factors word by word. A fixed 2 KiB transpose replaces
/// one 128-bit linear-map lookup per lane. Verifiers stream these rows; provers
/// retain them across the challenge boundary for their second field sum.
fn coordinate_rows(claim: &Claim) -> impl Iterator<Item = (usize, [E; 128])> + '_ {
    let factors: Vec<_> = claim
        .factors
        .iter()
        .filter_map(|factor| coordinate(&factor.lanes).map(|lane| (lane, factor.words.as_slice())))
        .collect();
    let count = factors
        .iter()
        .map(|(_, words)| words.len())
        .max()
        .unwrap_or(0);
    (0..count).filter_map(move |word| {
        let mut row = [E::from(0); 128];
        for &(lane, words) in &factors {
            if let Some(k) = words.get(word) {
                row[lane].xor_in_place(k);
            }
        }
        if row.iter().all(|k| *k == E::from(0)) {
            return None;
        }
        Some((word, dual_coordinate_numerators(&row)))
    })
}
/// Six-bit public-coordinate tables fit in a small contiguous working set.
/// Every index depends on public coefficients, never on a witness coordinate.
fn accumulate_map(weights: &mut [E], coefficients: &[E], images: &[E; 128], f: &F) {
    const BITS: usize = 6;
    const VALUES: usize = 1 << BITS;
    let mut table = vec![[E::from(0); VALUES]; 128usize.div_ceil(BITS)];
    for (h, row) in table.iter_mut().enumerate() {
        let width = (128 - h * BITS).min(BITS);
        for v in 1usize..1 << width {
            row[v] = f.addf(
                &row[v & (v - 1)],
                &images[h * BITS + v.trailing_zeros() as usize],
            );
        }
    }
    for (w, a) in weights.iter_mut().zip(coefficients) {
        if *a == E::from(0) {
            continue;
        }
        let mut bits = a.to_u128();
        for row in &table {
            w.xor_in_place(&row[(bits & (VALUES as u128 - 1)) as usize]);
            bits >>= BITS;
        }
    }
}
cfg_prover! {pub(super) mod prover;}
cfg_verifier! {pub(super) mod verifier;}
