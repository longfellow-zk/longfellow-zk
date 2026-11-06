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

//! Express the v1 sumcheck checks as sparse constraints on inputs and hidden pads.
//!
//! A PadExpression stores a constant and a sparse list of (logical pad,
//! coefficient) terms. Every round scales the existing claim by L1, adds the
//! public messages with weights L0-L1 and L2, and introduces their matching pad
//! terms. A layer ends with C-Q*A*B=0, where Q is the fully bound wiring tensor
//! and A,B are the two unmasked witness claims.
//!
//! Expanding A and B leaves an affine pad expression and one product of the
//! final-claim pads. LayerRelation stores those two parts. InputRelation stores
//! the final dense input weights and the negated combined claim, giving
//! sum_i weights[i]*inputs[i] + linear(pads) = 0. The ZK v1 compiler assigns
//! committed coordinates; the numerical verifier can evaluate the same objects.
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::RuntimeField,
        sumcheck_v1::{RoundPoly, SumcheckProof, VerifierData},
    },
};

/// A logical additive pad, independent of its location in a commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pad {
    Round {
        layer: usize,
        round: usize,
        hand: usize,
        /// Wire slot: 0 masks p(0), 1 masks p(pt(2)); p(1) follows from the claim.
        evaluation: usize,
    },
    Endpoint {
        layer: usize,
        /// Final witness claim: hand 0 is r, hand 1 is l.
        endpoint: usize,
    },
}

#[derive(Debug)]
pub struct PadTerm<E> {
    pub pad: Pad,
    pub coefficient: E,
}

/// A constant plus a linear combination of logical pads.
#[derive(Debug)]
pub struct PadExpression<E> {
    pub constant: E,
    pub terms: Vec<PadTerm<E>>,
}

/// This layer accepts when linear + product_coefficient * pad[0] * pad[1] = 0.
#[derive(Debug)]
pub struct LayerRelation<E> {
    pub linear: PadExpression<E>,
    pub product_coefficient: E,
}

/// The final relation is dot(weights, inputs) + linear = 0.
#[derive(Debug)]
pub struct InputRelation<E> {
    pub weights: Vec<E>,
    pub linear: PadExpression<E>,
}

#[derive(Debug)]
pub struct VerificationRelations<E> {
    pub layers: Vec<LayerRelation<E>>,
    pub input: InputRelation<E>,
}

/// Construct constraints from locally produced verifier data.
/// Consumes the data so the final dense weights move into the input relation.
/// Constructing relations does not establish that they are satisfied.
pub fn verify<const W: usize, F: RuntimeField<W> + SerializableField>(
    proof: &SumcheckProof<W, F>,
    data: VerifierData<F::E>,
    f: &F,
) -> Result<VerificationRelations<F::E>, String> {
    if proof.layers.len() != data.layers.len() {
        return Err("sumcheck verifier data layer count mismatch".into());
    }
    let mut layers = Vec::with_capacity(proof.layers.len());
    for (layer, layer_data) in data.layers.into_iter().enumerate() {
        let messages = &proof.layers[layer];
        let rounds = messages.hp[0].len();
        if messages.hp[1].len() != rounds
            || layer_data.rounds.iter().any(|hand| hand.len() != rounds)
        {
            return Err("sumcheck verifier data round count mismatch".into());
        }
        let mut claim = if layer == 0 {
            PadExpression {
                constant: f.zero(),
                terms: Vec::new(),
            }
        } else {
            endpoint_claim(
                layer - 1,
                &proof.layers[layer - 1].claims,
                &layer_data.alpha,
                f,
            )
        };
        claim.terms.reserve(4 * rounds + 2);
        for round in 0..rounds {
            for hand in 0..2 {
                let message = &messages.hp[hand][round];
                let coefficients = &layer_data.rounds[hand][round];
                f.mul(&mut claim.constant, &coefficients.l1);
                for term in &mut claim.terms {
                    f.mul(&mut term.coefficient, &coefficients.l1);
                }
                f.fma(
                    &mut claim.constant,
                    &coefficients.l0_minus_l1,
                    &message.evaluations[0],
                );
                f.fma(
                    &mut claim.constant,
                    &coefficients.l2,
                    &message.evaluations[1],
                );
                for (evaluation, coefficient) in [&coefficients.l0_minus_l1, &coefficients.l2]
                    .into_iter()
                    .enumerate()
                {
                    claim.terms.push(PadTerm {
                        pad: Pad::Round {
                            layer,
                            round,
                            hand,
                            evaluation,
                        },
                        coefficient: coefficient.clone(),
                    });
                }
            }
        }
        let product = f.mulf(&messages.claims[0], &messages.claims[1]);
        f.sub(
            &mut claim.constant,
            &f.mulf(&layer_data.bound_quad, &product),
        );
        for endpoint in 0..2 {
            claim.terms.push(PadTerm {
                pad: Pad::Endpoint { layer, endpoint },
                coefficient: f.neg(&f.mulf(&layer_data.bound_quad, &messages.claims[1 - endpoint])),
            });
        }
        layers.push(LayerRelation {
            linear: claim,
            product_coefficient: f.neg(&layer_data.bound_quad),
        });
    }
    let mut claim = match proof.layers.last() {
        Some(last) => endpoint_claim(proof.layers.len() - 1, &last.claims, &data.input_alpha, f),
        None => PadExpression {
            constant: f.zero(),
            terms: Vec::new(),
        },
    };
    claim.constant = f.neg(&claim.constant);
    for term in &mut claim.terms {
        term.coefficient = f.neg(&term.coefficient);
    }
    Ok(VerificationRelations {
        layers,
        input: InputRelation {
            weights: data.input_weights,
            linear: claim,
        },
    })
}

fn endpoint_claim<const W: usize, F: RuntimeField<W>>(
    layer: usize,
    messages: &[F::E; 2],
    alpha: &F::E,
    f: &F,
) -> PadExpression<F::E> {
    PadExpression {
        constant: f.addf(&messages[0], &f.mulf(alpha, &messages[1])),
        terms: vec![
            PadTerm {
                pad: Pad::Endpoint { layer, endpoint: 0 },
                coefficient: f.one(),
            },
            PadTerm {
                pad: Pad::Endpoint { layer, endpoint: 1 },
                coefficient: alpha.clone(),
            },
        ],
    }
}

impl<E: Clone> VerificationRelations<E> {
    /// Evaluate the logical relations using revealed inputs and pads.
    /// Returns one residual per layer followed by the input residual; all must be zero.
    pub fn evaluate<const W: usize, F: RuntimeField<W, E = E> + SerializableField>(
        &self,
        inputs: &[E],
        pads: &SumcheckProof<W, F>,
        f: &F,
    ) -> Result<Vec<E>, String> {
        if pads.layers.len() != self.layers.len() || inputs.len() != self.input.weights.len() {
            return Err("sumcheck relation input shape mismatch".into());
        }
        let mut residuals = Vec::with_capacity(self.layers.len() + 1);
        for (relation, layer_pads) in self.layers.iter().zip(&pads.layers) {
            let mut value = relation.linear.evaluate(pads, f)?;
            f.fma(
                &mut value,
                &relation.product_coefficient,
                &f.mulf(&layer_pads.claims[0], &layer_pads.claims[1]),
            );
            residuals.push(value);
        }
        let mut value = self.input.linear.evaluate(pads, f)?;
        f.add(
            &mut value,
            &crate::runtime::algebra::blas::dot(&self.input.weights, inputs, f),
        );
        residuals.push(value);
        Ok(residuals)
    }
}

impl<E: Clone> PadExpression<E> {
    fn evaluate<const W: usize, F: RuntimeField<W, E = E> + SerializableField>(
        &self,
        pads: &SumcheckProof<W, F>,
        f: &F,
    ) -> Result<E, String> {
        let mut value = self.constant.clone();
        for term in &self.terms {
            let pad = match term.pad {
                Pad::Round {
                    layer,
                    round,
                    hand,
                    evaluation,
                } => pads
                    .layers
                    .get(layer)
                    .and_then(|layer_pads| {
                        layer_pads.hp.get(hand).and_then(|rounds| rounds.get(round))
                    })
                    .and_then(|RoundPoly { evaluations }| evaluations.get(evaluation)),
                Pad::Endpoint { layer, endpoint } => pads
                    .layers
                    .get(layer)
                    .and_then(|layer_pads| layer_pads.claims.get(endpoint)),
            }
            .ok_or("sumcheck relation pad shape mismatch")?;
            f.fma(&mut value, &term.coefficient, pad);
        }
        Ok(value)
    }
}
