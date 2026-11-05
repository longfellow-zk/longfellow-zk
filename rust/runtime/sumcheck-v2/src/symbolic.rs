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

//! Reduce sumcheck verification to constraints on committed circuit inputs and pads.
//!
//! Sumcheck starts with the claim that the circuit's outputs are zero. Working
//! through the circuit from outputs to inputs, it reduces each layer's claim to
//! two claims on that layer's inputs, then combines them into one claim for the
//! next layer. The last claim must equal a weighted sum of the circuit inputs.
//!
//! Within a layer, each round binds one wire-index coordinate at a sampled field
//! challenge z. The tables hold monomial coefficients: binding maps (a,b) to
//! a + z*b. The quadratic round polynomial is p(x) = c0 + c1*x + c2*x^2.
//! Its constant and quadratic coefficients sum to the incoming claim C, so the
//! two supplied coefficients c0,c1 determine the next claim:
//!
//! ```text
//! C' = p(z) = z^2*C + (1-z^2)*c0 + z*c1.
//! ```
//!
//! In Longfellow v2, the prover first commits to the private inputs, secret pads,
//! and the products of each layer's two final-claim pads. It then sends sumcheck
//! messages with those pads subtracted. Both parties derive the same public
//! challenges and final input weights from the circuit and the masked transcript.
//!
//! `build_constraints` updates the claims with pads as symbolic variables: each
//! unmasked coefficient is its message plus its pad. The update above is linear
//! in C,c0,c1, so the running claim is affine in the pads. At each layer's end,
//! the final evaluations of `W` and `q_l`, called `A` and `B`, must satisfy:
//!
//! ```text
//! A = m_A + p_A,  B = m_B + p_B
//! claim - A*B = 0
//! claim_next = A + alpha*B.
//! ```
//!
//! Expanding `claim - A*B` leaves an affine expression minus `p_A*p_B`. We record
//! that constraint and continue with `claim_next`. At the end we also record
//! `claim - sum_i input_weights[i] * W[i] = 0`, where `W` is now the circuit input.
//! Affine pad expressions use sparse lists of `(pad, coefficient)` terms; the
//! final input weights are dense. All constants and coefficients are public.
//!
//! Both prover and verifier pass these constraints to the v2 constraint compiler.
//! It substitutes public inputs, maps symbolic pads to committed positions, and
//! uses the committed product slots for `p_A*p_B`. Polygero proves and verifies
//! the resulting linear constraints and the constraints on those product slots.
//! Thus each circuit layer contributes one linear constraint and one pad-product
//! constraint, followed by one final linear constraint connecting the input claim
//! to the committed inputs.

use crate::{
    core::algebra::SerializableField,
    runtime::{algebra::RuntimeField, sumcheck_v2::SumcheckProof},
};

/// Propagate an affine claim through the proof and record the constraints.
/// The initial claim is zero because the circuit's outputs must vanish. After
/// each layer's rounds, constrain the claim to `A * B`, then start the next layer
/// with `A + alpha * B`. Finally constrain the claim to the weighted input sum.
pub(crate) fn build_constraints<const W: usize, F: RuntimeField<W> + SerializableField>(
    proof: &SumcheckProof<W, F>,
    layer_challenges: Vec<LayerChallenges<F::E>>,
    input_weights: Vec<F::E>,
    f: &F,
) -> Constraints<F::E> {
    assert_eq!(
        proof.layers.len(),
        layer_challenges.len(),
        "sumcheck challenge layer count mismatch"
    );
    let mut claim = PadExpression {
        constant: f.zero(),
        terms: Vec::new(),
    };
    let mut layers = Vec::with_capacity(proof.layers.len());
    for (layer, challenges) in layer_challenges.into_iter().enumerate() {
        f.sub(&mut claim.constant, &challenges.constant);
        let messages = &proof.layers[layer];
        assert_eq!(
            messages.rounds.len(),
            challenges.point_l.len(),
            "sumcheck challenge round count mismatch"
        );
        claim.terms.reserve(2 * messages.rounds.len() + 2);
        for (round, z) in challenges.point_l.into_iter().enumerate() {
            claim.round(layer, round, &messages.rounds[round].coefficients, &z, f);
        }
        claim.subtract_claim_product(layer, &messages.claims, f);
        layers.push(claim);
        let correction = f.mulf(&challenges.alpha, &challenges.linear);
        claim = PadExpression::claim_next(layer, &messages.claims, challenges.alpha, f);
        f.sub(&mut claim.constant, &correction);
    }
    Constraints {
        layers,
        input_claim: claim,
        input_weights,
    }
}

/// Constraints produced by symbolically running all rounds and layer transitions.
/// Each layer contributes one product constraint; the final constraint connects
/// the last claim to the circuit inputs.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Constraints<E> {
    /// For layer `j`: `layers[j] - p_A[j] * p_B[j] = 0`.
    /// Only the affine part is stored; the pad-product term is implicit.
    pub(crate) layers: Vec<PadExpression<E>>,
    /// Final claim, giving `input_claim - sum_i input_weights[i] * W[i] = 0`.
    pub(crate) input_claim: PadExpression<E>,
    /// One coefficient per circuit input, including public inputs.
    pub(crate) input_weights: Vec<E>,
}

/// Sparse affine expression `constant + sum_{(pad, k) in terms} k * pad`.
/// The constant and coefficients are known field elements; pads remain variables.
/// A term list suffices because each referenced pad is appended once.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct PadExpression<E> {
    pub(crate) constant: E,
    pub(crate) terms: Vec<(Pad, E)>,
}

/// A symbolic variable naming a secret pad by the proof value it masks.
/// This lets constraints refer to pads before assigning committed witness positions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Pad {
    /// Pad subtracted from one of a round's two polynomial coefficients.
    Round {
        /// Zero-based layer index, from circuit outputs toward inputs.
        layer: usize,
        /// Zero-based round index within that layer.
        round: usize,
        /// Position in the round's two-coefficient message:
        /// `0` names `s0` in `message[0] = c0 - s0`;
        /// `1` names `s1` in `message[1] = c1 - s1`.
        /// Here p(x) = c0 + c1*x + c2*x^2 and c2 = claim - c0.
        slot: usize,
    },
    /// Pad subtracted from one of the layer's two final claims.
    Claim {
        /// Zero-based layer index, from circuit outputs toward inputs.
        layer: usize,
        /// Position in the layer's two-claim message:
        /// `0` names `p_A` in `message[0] = A - p_A`;
        /// `1` names `p_B` in `message[1] = B - p_B`.
        slot: usize,
    },
}

impl<E: Clone> PadExpression<E> {
    /// Update `self` from the incoming claim c0 + c2 to the next claim p(z).
    /// Binding the next coordinate to z leaves one fewer wire-index bit to sum.
    ///
    /// The messages hide two coefficients: m[0] = c0 - s0 and m[1] = c1 - s1,
    /// where s0,s1 are secret pads. Since c2 = claim - c0:
    ///
    /// ```text
    /// claim' = p(z)
    ///        = c0 + z*c1 + z^2*(claim - c0)
    ///        = z^2*claim + (1-z^2)*(m[0] + s0) + z*(m[1] + s1).
    /// ```
    ///
    /// Both claims are affine expressions in the pads. The old terms scale by z^2;
    /// the new pads s0,s1 receive coefficients 1-z^2 and z.
    fn round<const W: usize, F: RuntimeField<W, E = E>>(
        &mut self,
        layer: usize,
        round: usize,
        m: &[E; 2],
        z: &E,
        f: &F,
    ) {
        let z2 = f.mulf(z, z);
        // Substituting c2 = claim - c0 gives c0 the coefficient 1 - z^2.
        let one_minus_z2 = f.subf(&f.one(), &z2);
        let s0 = Pad::Round {
            layer,
            round,
            slot: 0,
        };
        let s1 = Pad::Round {
            layer,
            round,
            slot: 1,
        };

        // Constant part of claim': z^2*constant + (1-z^2)*m[0] + z*m[1].
        f.mul(&mut self.constant, &z2);
        f.fma(&mut self.constant, &one_minus_z2, &m[0]);
        f.fma(&mut self.constant, z, &m[1]);
        // Scale all existing symbolic terms by z^2, the multiplier of the old claim.
        for (_, k) in &mut self.terms {
            f.mul(k, &z2);
        }
        // Finally, add the new symbolic terms (1-z^2)*s0 and z*s1.
        self.terms.extend([(s0, one_minus_z2), (s1, z.clone())]);
    }

    /// Form the affine part of the constraint `claim - A*B = 0`:
    ///
    /// ```text
    /// claim - m_A*m_B - m_B*p_A - m_A*p_B.
    /// ```
    ///
    /// The remaining term `-p_A*p_B` is implicit in `Constraints::layers`.
    fn subtract_claim_product<const W: usize, F: RuntimeField<W, E = E>>(
        &mut self,
        layer: usize,
        messages: &[E; 2],
        f: &F,
    ) {
        let [m_a, m_b] = messages;
        // Subtract the constant m_A*m_B in (m_A+p_A)*(m_B+p_B).
        f.fnms(&mut self.constant, m_a, m_b);
        // The two cross terms are -m_B*p_A and -m_A*p_B; their signs are
        // already those of the constraint and pass unchanged to the compiler.
        self.terms.extend([
            (Pad::Claim { layer, slot: 0 }, f.neg(m_b)),
            (Pad::Claim { layer, slot: 1 }, f.neg(m_a)),
        ]);
    }

    /// Combine `A` and `B` into one claim for the next layer:
    /// `(m_A + alpha*m_B) + p_A + alpha*p_B`.
    /// Earlier round pads occur only in the constraint just recorded; this new
    /// claim depends only on the two final-claim pads.
    fn claim_next<const W: usize, F: RuntimeField<W, E = E>>(
        layer: usize,
        messages: &[E; 2],
        alpha: E,
        f: &F,
    ) -> Self {
        let mut constant = messages[0].clone();
        f.fma(&mut constant, &alpha, &messages[1]);
        Self {
            constant,
            terms: vec![
                (Pad::Claim { layer, slot: 0 }, f.one()),
                (Pad::Claim { layer, slot: 1 }, alpha),
            ],
        }
    }
}

/// The sampled round challenges form `point_l`, the point at which the layer's
/// wire index is bound. `alpha` combines the two final claims as `A + alpha * B`
/// to give the claim for the next layer.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct LayerChallenges<E> {
    /// Public constant contribution to subtract before the dot-product rounds.
    pub(crate) constant: E,
    /// Public linear evaluation to subtract from the final B claim.
    pub(crate) linear: E,
    pub(crate) point_l: Vec<E>,
    pub(crate) alpha: E,
}
