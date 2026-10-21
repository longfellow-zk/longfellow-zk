// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Protocol-derived scalars and final public weights for constraint construction.
//! These values are local computation results, never part of the proof codec.
use crate::{LagrangeBasis, RoundPoly};
use core_algebra::SerializableField;
use runtime_algebra::{InterpolationField, RuntimeField};

/// Evaluate a quadratic round as L1 * claim + (L0-L1) * g(0) + L2 * g(2).
#[derive(Debug, PartialEq, Eq)]
pub struct RoundCoefficients<E> {
    pub l1: E,
    pub l0_minus_l1: E,
    pub l2: E,
}

impl<E> RoundCoefficients<E> {
    pub fn new<const W: usize, F: InterpolationField<W, E = E>>(
        basis: &LagrangeBasis<3, W, F>,
        challenge: &E,
        f: &F,
    ) -> Self {
        let [l0, l1, l2] = basis.coef(challenge, f).evaluations;
        let l0_minus_l1 = f.subf(&l0, &l1);
        Self {
            l1,
            l0_minus_l1,
            l2,
        }
    }

    pub fn evaluate<const W: usize, F: RuntimeField<W, E = E> + SerializableField>(
        &self,
        polynomial: &RoundPoly<W, F>,
        claim: &E,
        f: &F,
    ) -> E {
        let mut value = f.mulf(&self.l1, claim);
        f.fma(&mut value, &self.l0_minus_l1, &polynomial.evaluations[0]);
        f.fma(&mut value, &self.l2, &polynomial.evaluations[1]);
        value
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct LayerVerifierData<E> {
    pub rounds: [Vec<RoundCoefficients<E>>; 2],
    pub bound_quad: E,
    pub alpha: E,
}

/// Trusted output of numerical proving or independent verifier derivation.
/// Verification must derive this data itself, never receive it from a proof.
/// Only per-round and per-layer scalars and the final dense weights are retained.
#[derive(Debug, PartialEq, Eq)]
pub struct VerifierData<E> {
    pub layers: Vec<LayerVerifierData<E>>,
    pub input_alpha: E,
    pub input_weights: Vec<E>,
}
