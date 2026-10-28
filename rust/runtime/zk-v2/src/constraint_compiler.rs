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
//! The committed vector starts with packed private inputs and packing masks,
//! followed by each layer's round pads and final-claim pads p_A,p_B,p_A*p_B. Symbolic sumcheck
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
//! become a logical claim handed to dual packing. Every emitted backend equation
//! has the form sum_w A[c,w]*w+b[c]=0.
//!
//! Both roles run this transformation after sumcheck. Product constraints and
//! committed positions are fixed separately when preparing the circuit layout.
use crate::runtime::{
    algebra::RuntimeField,
    polygero::PolygeroLinearTerm,
    proto::sumcheck_v2::CircuitPadLayout,
    sumcheck_v2::symbolic::{Constraints, Pad, PadExpression},
};

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

/// Consume symbolic constraints, moving their only dense input-weight vector.
pub(super) fn compile<const W: usize, F: RuntimeField<W>>(
    mut constraints: Constraints<F::E>,
    pads: &CircuitPadLayout,
    public: &[F::E],
    layout: &crate::runtime::proto::zk_v2::PackingLayout,
    f: &F,
) -> Result<super::commitment::CommitmentStatement<F::E>, String> {
    use crate::runtime::dual_packing::generic::{Affine, SourceClaim};
    if constraints.input_weights.len() != public.len() + layout.private_inputs {
        return Err("input claim shape".into());
    }
    let (a, b) = compile_layers(&constraints, pads, f)?;
    let constant = f.subf(
        &constraints.input_claim.constant,
        &crate::runtime::algebra::blas::dot(&constraints.input_weights[..public.len()], public, f),
    );
    let terms = constraints
        .input_claim
        .terms
        .into_iter()
        .map(|(p, k)| pad_coordinate(p, pads).map(|w| (w - layout.suffix_start, k)))
        .collect::<Result<Vec<_>, _>>()?;
    constraints.input_weights.drain(..public.len());
    Ok(super::commitment::CommitmentStatement {
        claim: SourceClaim {
            weights: constraints.input_weights,
            rhs: Affine { constant, terms },
            auxiliary_count: layout.pad_cells,
        },
        a,
        b,
    })
}
