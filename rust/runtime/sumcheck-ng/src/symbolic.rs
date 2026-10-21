// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Pure sumcheck acceptance relations over logical inputs and additive pads.
//! No transcript, commitment coordinates, or commitment-system types belong here.
use crate::{RoundPoly, SumcheckProof, VerifierData};
use core_algebra::SerializableField;
use runtime_algebra::RuntimeField;

/// A logical additive pad, independent of its location in a commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pad {
    Round {
        layer: usize,
        round: usize,
        evaluation: usize,
    },
    Endpoint {
        layer: usize,
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

/// This layer accepts when linear - endpoint_pad[0] * endpoint_pad[1] = 0.
#[derive(Debug)]
pub struct LayerRelation<E> {
    pub linear: PadExpression<E>,
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

/// Construct acceptance equations from locally produced verifier data.
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
    let mut claim = PadExpression {
        constant: f.zero(),
        terms: Vec::new(),
    };
    let mut layers = Vec::with_capacity(proof.layers.len());
    for (layer, (messages, layer_data)) in proof.layers.iter().zip(data.layers).enumerate() {
        if messages.rounds.len() != layer_data.rounds.len() {
            return Err("sumcheck verifier data round count mismatch".into());
        }
        claim.terms.reserve(2 * messages.rounds.len() + 2);
        for (round, (message, coefficients)) in
            messages.rounds.iter().zip(layer_data.rounds).enumerate()
        {
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
            for (evaluation, coefficient) in [coefficients.l0_minus_l1, coefficients.l2]
                .into_iter()
                .enumerate()
            {
                claim.terms.push(PadTerm {
                    pad: Pad::Round {
                        layer,
                        round,
                        evaluation,
                    },
                    coefficient,
                });
            }
        }
        // claim = (message_A + pad_A) * (message_B + pad_B).
        f.sub(
            &mut claim.constant,
            &f.mulf(&messages.claims[0], &messages.claims[1]),
        );
        for endpoint in 0..2 {
            claim.terms.push(PadTerm {
                pad: Pad::Endpoint { layer, endpoint },
                coefficient: f.neg(&messages.claims[1 - endpoint]),
            });
        }
        layers.push(LayerRelation { linear: claim });
        // The next layer starts from A + alpha B.
        claim = PadExpression {
            constant: f.addf(
                &messages.claims[0],
                &f.mulf(&layer_data.alpha, &messages.claims[1]),
            ),
            terms: vec![
                PadTerm {
                    pad: Pad::Endpoint { layer, endpoint: 0 },
                    coefficient: f.one(),
                },
                PadTerm {
                    pad: Pad::Endpoint { layer, endpoint: 1 },
                    coefficient: layer_data.alpha,
                },
            ],
        };
    }
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
            f.sub(
                &mut value,
                &f.mulf(&layer_pads.claims[0], &layer_pads.claims[1]),
            );
            residuals.push(value);
        }
        let mut value = self.input.linear.evaluate(pads, f)?;
        f.add(
            &mut value,
            &runtime_algebra::blas::dot(&self.input.weights, inputs, f),
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
                    evaluation,
                } => pads
                    .layers
                    .get(layer)
                    .and_then(|layer_pads| layer_pads.rounds.get(round))
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
