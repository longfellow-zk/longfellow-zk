// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Reference for the untransformed degree-one input equation.
use super::*;
use crate::runtime::algebra::ElementOf;
/// Emit one equation per circuit layer and one final input equation, in that order.
/// Preserve all terms, including zero coefficients; repeated terms remain additive.
/// Equations and their constants remain even when every variable coefficient vanishes.
pub(in crate::runtime::zk_v2) fn compile<const W: usize, F: RuntimeField<W>>(
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
