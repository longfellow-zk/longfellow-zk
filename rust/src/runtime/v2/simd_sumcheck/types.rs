// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    core::proto::sane_logw,
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        v2::proto::simd::SimdProof,
    },
};
pub(super) const MASKS: usize = 129;
pub(super) type Proof = SimdProof<Gf2_128Field>;
#[derive(Clone, Copy, Debug)]
pub(super) struct Product {
    pub g: usize,
    pub l: usize,
    pub r: usize,
}
#[derive(Clone, Debug)]
pub(crate) struct NativeRow {
    pub constant: Gf2_128,
    pub terms: Vec<(usize, Gf2_128)>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Challenges {
    pub point: Vec<Gf2_128>,
    pub alpha: Gf2_128,
    pub terminal: Gf2_128,
}

pub(super) fn rounds(products: usize) -> Result<usize, String> {
    if products == 0 {
        return Err("SIMD needs at least one product".into());
    }
    let count = products
        .checked_mul(128)
        .and_then(usize::checked_next_power_of_two)
        .ok_or("SIMD product dimensions")?;
    let rounds = count.ilog2() as usize;
    if !sane_logw(rounds) {
        return Err("SIMD product dimensions".into());
    }
    Ok(rounds)
}

cfg_prover! {pub(super) mod prover;}
