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

//! Protocol-derived scalars and final public weights for constraint construction.
//! These values are local computation results, never part of the proof codec.
//!
//! If L0,L1,L2 are the quadratic Lagrange weights at a challenge, then
//! p(z)=L1*claim+(L0-L1)*p(0)+L2*p(pt(2)). Each RoundCoefficients stores exactly
//! those three multipliers. LayerVerifierData also records the two-claim mixing
//! scalar and the fully bound QUAD value; the final input weights are dense.
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{InterpolationField, RuntimeField},
        sumcheck_v1::{LagrangeBasis, RoundPoly},
    },
};

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
