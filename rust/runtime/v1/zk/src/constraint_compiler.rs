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

//! Compile v1 sumcheck constraints into Ligero's sparse A*w+b=0 representation.
//!
//! Each layer contributes one equation in message pads, endpoint pads, and their
//! committed product. The final equation also contains circuit inputs: public
//! inputs contribute to b, while private inputs contribute columns of A. Logical
//! pad indices are resolved through the same layout used to build the commitment.
//! A separate product constraint enforces each committed pad product x*y=z.
use crate::runtime::{
    algebra::{ElementOf, RuntimeField},
    v1::{
        ligero::param::{LigeroLinearConstraint, LigeroQuadraticConstraint},
        proto::sumcheck::{CircuitPadLayout, SumcheckProofGeometry},
        sumcheck::symbolic::{Pad, PadExpression, VerificationRelations},
    },
};

/// Emit one equation per layer followed by the final input equation.
/// Preserve term order and coefficients, including zero coefficients.
pub fn compile<const W: usize, F: RuntimeField<W>>(
    relations: &VerificationRelations<ElementOf<F>>,
    pads: &CircuitPadLayout,
    public_inputs: &[ElementOf<F>],
    f: &F,
) -> Result<(Vec<LigeroLinearConstraint<W, F>>, Vec<ElementOf<F>>), String> {
    if relations.layers.len() != pads.layers.len() {
        return Err("sumcheck relation pad layer count mismatch".into());
    }
    if public_inputs.len() > relations.input.weights.len() {
        return Err("sumcheck relation public input length mismatch".into());
    }
    let (mut a, mut b) = (Vec::new(), Vec::with_capacity(relations.layers.len() + 1));
    for c in 0..relations.layers.len() {
        let relation = &relations.layers[c];
        append_pad_terms(&mut a, c, &relation.linear, pads)?;
        // The commitment includes z = pad_A * pad_B; its quadratic
        // consistency constraint is supplied by product_constraints.
        a.push(LigeroLinearConstraint {
            c,
            w: pads.layers[c].claims[2],
            k: relation.product_coefficient.clone(),
        });
        b.push(relation.linear.constant.clone());
    }
    let input = &relations.input;
    let c = b.len();
    let mut constant = input.linear.constant.clone();
    f.add(
        &mut constant,
        &crate::runtime::algebra::blas::dot(
            &input.weights[..public_inputs.len()],
            public_inputs,
            f,
        ),
    );
    b.push(constant);
    for (w, weight) in input.weights[public_inputs.len()..].iter().enumerate() {
        a.push(LigeroLinearConstraint {
            c,
            w,
            k: weight.clone(),
        });
    }
    append_pad_terms(&mut a, c, &input.linear, pads)?;
    Ok((a, b))
}

/// Resolve symbolic pad references to witness coordinates in equation `c`.
/// Preserve every coefficient and check every referenced coordinate.
fn append_pad_terms<const W: usize, F: RuntimeField<W>>(
    constraints: &mut Vec<LigeroLinearConstraint<W, F>>,
    c: usize,
    expression: &PadExpression<ElementOf<F>>,
    pads: &CircuitPadLayout,
) -> Result<(), String> {
    for term in &expression.terms {
        let w = match term.pad {
            Pad::Round {
                layer,
                round,
                hand,
                evaluation,
            } => pads
                .layers
                .get(layer)
                .and_then(|layer_pads| layer_pads.rounds.get(round))
                .and_then(|coordinates| coordinates.get(hand))
                .and_then(|pair| pair.get(evaluation)),
            Pad::Endpoint { layer, endpoint } => pads
                .layers
                .get(layer)
                .and_then(|layer_pads| layer_pads.claims[..2].get(endpoint)),
        }
        .ok_or("sumcheck relation pad shape mismatch")?;
        constraints.push(LigeroLinearConstraint {
            c,
            w: *w,
            k: term.coefficient.clone(),
        });
    }
    Ok(())
}

/// Constrain each committed endpoint-pad product, including during commitment.
#[must_use]
pub fn product_constraints(
    start_pad: usize,
    geometry: &SumcheckProofGeometry,
) -> Vec<LigeroQuadraticConstraint> {
    geometry
        .claim_indices(start_pad)
        .map(|[x, y, z]| LigeroQuadraticConstraint { x, y, z })
        .collect()
}

#[cfg(test)]
#[path = "../tests/constraint_compiler.rs"]
mod tests;
