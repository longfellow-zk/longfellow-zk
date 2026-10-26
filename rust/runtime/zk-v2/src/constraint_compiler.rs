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

//! Lower symbolic sumcheck constraints into Polygero's sparse A*w+b=0 format.
//!
//! The committed vector starts with private circuit inputs, followed by each
//! layer's round pads and final-claim pads p_A,p_B,p_A*p_B. Symbolic sumcheck
//! expressions instead name pads by (layer, round, slot), independently of this
//! physical layout. Compilation replaces each logical pad with its committed
//! coordinate and substitutes the known public-input prefix.
//!
//! A layer supplies E(p) = c + sum_{(p,k) in terms} k*p, with the constraint
//!
//! ```text
//! sum_{(p,k) in terms} k*w[coordinate(p)] - w[product_slot] + c = 0.
//! ```
//!
//! The product slot holds p_A*p_B. Preserve E's signed coefficients and constant;
//! the coefficient -1 restores the product term left implicit by sumcheck.
//! The final input constraint subtracts the weighted circuit inputs from the
//! last claim. Public input terms become constants in b; private input terms
//! become coefficients in A. Every emitted equation has the form sum_w A[c,w]*w+b[c]=0.
//!
//! Both roles run this transformation after sumcheck. Product constraints and
//! committed positions are fixed separately when preparing the circuit layout.
use crate::runtime::{
    algebra::{blas, ElementOf, RuntimeField},
    polygero::PolygeroLinearTerm,
    proto::sumcheck_v2::CircuitPadLayout,
    sumcheck_v2::symbolic::{Constraints, Pad, PadExpression},
};

/// Emit one equation per circuit layer and one final input equation, in that order.
/// Preserve all terms, including zero coefficients; repeated terms remain additive.
/// Equations and their constants remain even when every variable coefficient vanishes.
pub(super) fn compile<const W: usize, F: RuntimeField<W>>(
    constraints: &Constraints<ElementOf<F>>,
    pads: &CircuitPadLayout,
    public_inputs: &[ElementOf<F>],
    f: &F,
) -> Result<(Vec<PolygeroLinearTerm<ElementOf<F>>>, Vec<ElementOf<F>>), String> {
    validate(constraints, pads, public_inputs.len())?;
    let (mut a, mut b) = compile_layers(constraints, pads, f)?;
    append_input_constraint(&mut a, &mut b, constraints, pads, public_inputs, f)?;
    Ok((a, b))
}

/// Compile GKR layer equations without allocating a direct-field input row.
pub(super) fn compile_layers<const W: usize, F: RuntimeField<W>>(
    constraints: &Constraints<F::E>,
    pads: &CircuitPadLayout,
    f: &F,
) -> Result<(Vec<PolygeroLinearTerm<F::E>>, Vec<F::E>), String> {
    validate(constraints, pads, 0)?;
    let (mut a, mut b) = (Vec::new(), Vec::with_capacity(constraints.layers.len() + 1));
    for c in 0..constraints.layers.len() {
        let constraint = &constraints.layers[c];
        append_pad_terms(&mut a, c, constraint, pads)?;
        // E(p) - p_A*p_B = 0: the product slot contributes with coefficient -1.
        a.push(PolygeroLinearTerm {
            c,
            w: pads.layers[c].claims[2],
            k: f.mone(),
        });
        b.push(constraint.constant.clone());
    }
    Ok((a, b))
}

/// Emit the final input equation, with N public inputs and weights a_i:
///
/// ```text
/// sum_{(p,k) in claim.terms} k*w[coordinate(p)]
///   + sum_{j=0}^{nprivate-1} (-a_{N+j})*w[j]
///   + (claim.constant - sum_{i=0}^{N-1} a_i*public[i]) = 0.
/// ```
/// Pad coefficients already have their constraint signs and pass through unchanged.
fn append_input_constraint<const W: usize, F: RuntimeField<W>>(
    a: &mut Vec<PolygeroLinearTerm<F::E>>,
    b: &mut Vec<F::E>,
    constraints: &Constraints<F::E>,
    pads: &CircuitPadLayout,
    public_inputs: &[F::E],
    f: &F,
) -> Result<(), String> {
    let claim = &constraints.input_claim;
    let weights = &constraints.input_weights;
    let npublic = public_inputs.len();
    let c = b.len();
    // The input sum is subtracted from the claim, so its known public part
    // contributes -sum_i a_i*public[i] to the constant b[c].
    let public_sum = blas::dot(&weights[..npublic], public_inputs, f);
    b.push(f.subf(&claim.constant, &public_sum));
    for w in 0..weights.len() - npublic {
        let weight = &weights[npublic + w];
        a.push(PolygeroLinearTerm {
            c,
            w,
            // Subtract the private part of that same sum, once.
            k: f.neg(weight),
        });
    }
    append_pad_terms(a, c, claim, pads)
}

/// Bind logical pads to committed slots, preserving every coefficient.
fn append_pad_terms<E: Clone>(
    a: &mut Vec<PolygeroLinearTerm<E>>,
    c: usize,
    expression: &PadExpression<E>,
    pads: &CircuitPadLayout,
) -> Result<(), String> {
    for (pad, coefficient) in &expression.terms {
        let w = pad_coordinate(*pad, pads)?;
        a.push(PolygeroLinearTerm {
            c,
            w,
            k: coefficient.clone(),
        });
    }
    Ok(())
}

/// Resolve a logical pad while checking every layer/round/slot index. Claim
/// expressions can reference p_A and p_B; their product slot is emitted separately.
pub(super) fn pad_coordinate(pad: Pad, pads: &CircuitPadLayout) -> Result<usize, String> {
    match pad {
        Pad::Round { layer, round, slot } => pads
            .layers
            .get(layer)
            .and_then(|layer_pads| layer_pads.rounds.get(round))
            .and_then(|coordinates| coordinates.get(slot)),
        Pad::Claim { layer, slot } => pads
            .layers
            .get(layer)
            .and_then(|layer_pads| layer_pads.claims[..2].get(slot)),
    }
    .copied()
    .ok_or_else(|| "sumcheck constraint pad shape mismatch".into())
}

/// Check the layer count and public prefix before indexing their shared layout.
/// Individual logical pad coordinates are checked when emitting their terms.
fn validate<E>(
    constraints: &Constraints<E>,
    pads: &CircuitPadLayout,
    npublic: usize,
) -> Result<(), String> {
    if constraints.layers.len() != pads.layers.len() {
        return Err("sumcheck constraint pad layer count mismatch".into());
    }
    if npublic > constraints.input_weights.len() {
        return Err("sumcheck constraint public input length mismatch".into());
    }
    Ok(())
}

#[cfg(test)]
#[path = "../tests/constraint_compiler.rs"]
mod tests;
