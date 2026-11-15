// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Retained trace-pairing adapter for a sum of separable packed-bit functionals.
//! Its two affine equations are authenticated against the original commitment.
use super::{NativeRow, E, F};
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            packing::{binary::Binary128Extension, PackingParameters},
            RuntimeField,
        },
        v2::{proto::simd::SimdAdapterProof, transcript::TranscriptRef},
    },
};
pub(super) type Parameters = PackingParameters<Binary128Extension>;
#[derive(Clone)]
pub(super) struct Factor {
    pub words: Vec<E>,
    pub lanes: [E; 128],
}
pub(super) struct Claim {
    pub factors: Vec<Factor>,
    pub rhs: NativeRow,
    pub auxiliary_count: usize,
}
pub(super) type Proof = SimdAdapterProof<E>;
pub(super) struct Equation {
    pub words: Vec<E>,
    pub auxiliary: Vec<(usize, E)>,
    pub masks: [E; 129],
    pub constant: E,
}
mod kernel;
mod transcript;
cfg_prover! {pub(super) mod prover;}
cfg_verifier! {pub(super) mod verifier;}
fn validate(claim: &Claim) -> Result<usize, String> {
    let n = claim
        .factors
        .iter()
        .map(|f| f.words.len())
        .max()
        .ok_or("empty SIMD factor list")?;
    if n == 0
        || claim
            .rhs
            .terms
            .iter()
            .any(|(i, _)| *i >= claim.auxiliary_count)
    {
        return Err("SIMD factor shape".into());
    }
    Ok(n)
}
fn validate_proof(p: &Parameters, proof: &Proof) -> Result<(), String> {
    if proof.u.iter().any(|x| p.trace(x) != E::from(0)) {
        return Err("SIMD adapter trace".into());
    }
    Ok(())
}
fn equations(
    p: &Parameters,
    claim: &Claim,
    proof: &Proof,
    delta: &[E; 128],
    words: Vec<E>,
) -> [Equation; 2] {
    let f = p.field();
    let gamma = delta.map(|x| f.mulf(&x, &x));
    let eliminate = |v: &[E; 128]| -> Vec<E> {
        (1..128)
            .map(|i| f.addf(&v[i], &f.mulf(&v[0], &p.basis()[i])))
            .collect()
    };
    let mut first = eliminate(delta);
    first.extend([f.one(), f.zero()]);
    let mut second = eliminate(&gamma);
    second.extend([f.zero(), f.one()]);
    let mut eta = f.zero();
    let mut constant = f.mulf(&proof.a, &proof.a);
    for ((g, dual), u) in gamma.iter().zip(p.dual()).zip(proof.u) {
        f.fma(&mut eta, g, dual);
        f.fma(&mut constant, g, &u);
    }
    f.fma(&mut constant, &eta, &claim.rhs.constant);
    [
        Equation {
            words: Vec::new(),
            auxiliary: Vec::new(),
            masks: first.try_into().unwrap(),
            constant: proof.a,
        },
        Equation {
            words,
            auxiliary: claim
                .rhs
                .terms
                .iter()
                .map(|(i, k)| (*i, f.mulf(&eta, k)))
                .collect(),
            masks: second.try_into().unwrap(),
            constant,
        },
    ]
}
#[cfg(test)]
mod tests;
