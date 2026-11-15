// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Batch the complete masked sumcheck rows into one authenticated linear claim.
//!
//! Fresh independent row weights cover every layer equation and the final
//! input equation. The pure split step (`split::SplitClaim::batch`) draws
//! them after every frontend message and uses them at once (transcript I8);
//! the resulting claim is reconstructed locally by both parties, and derived
//! coefficients are not absorbed.
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{blas, blas::dot, RuntimeField},
        v2::{
            polygero::PolygeroLinearTerm,
            sumcheck::{self, symbolic::Constraints},
        },
    },
};

pub struct LinearClaim<E> {
    pub weights: Vec<E>,
    pub target: E,
}

/// The unbatched rows of a frontend over its values `[private inputs |
/// pads]`: the compiled layer rows `A*v + b = 0` and the input equation
/// `<w, v> = t`.
pub(crate) type Rows<E> = ((Vec<PolygeroLinearTerm<E>>, Vec<E>), LinearClaim<E>);

/// The rows of `circuit` on `public` from its reduced `constraints`.
pub(crate) fn rows<const W: usize, F: RuntimeField<W> + SerializableField>(
    circuit: &Circuit<F>,
    public: &[F::E],
    constraints: Constraints<F::E>,
    f: &F,
) -> Result<Rows<F::E>, String> {
    let private = circuit
        .raw
        .ninput
        .checked_sub(circuit.raw.npublic_input)
        .ok_or("batched frontend public prefix")?;
    if public.len() != circuit.raw.npublic_input
        || constraints.input_weights.len() != circuit.raw.ninput
    {
        return Err("batched frontend input shape".into());
    }
    let geometry = sumcheck::circuit_geometry(&[circuit])?;
    if constraints.layers.len() != geometry.layers().len() {
        return Err("batched frontend layer count".into());
    }
    let count = private
        .checked_add(geometry.pad_count())
        .ok_or("batched frontend layout overflow")?;
    let pads = geometry.pad_layout(private);
    let layers = super::constraint_compiler::compile_layers(&constraints, &pads)?;
    // Input equation: <w_in, inputs> = constant + sum k*pad.
    let mut weights = vec![f.zero(); count];
    weights[..private].clone_from_slice(&constraints.input_weights[public.len()..]);
    for (pad, k) in constraints.input_claim.terms {
        let j = super::constraint_compiler::pad_coordinate(pad, &pads)?;
        f.sub(&mut weights[j], &k);
    }
    let target = f.subf(
        &constraints.input_claim.constant,
        &dot(&constraints.input_weights[..public.len()], public, f),
    );
    Ok((layers, LinearClaim { weights, target }))
}

/// Batch `rows` with `rho`, one weight per layer row and a last one for the
/// input equation: `sum_c rho_c (A_c v + b_c) - rho_L (<w, v> - t) = 0`,
/// written as the claim `<weights, v> = target`.
pub(crate) fn batch<const W: usize, F: RuntimeField<W> + SerializableField>(
    rows: Rows<F::E>,
    rho: &[F::E],
    f: &F,
) -> Result<LinearClaim<F::E>, String> {
    let ((a, b), input) = rows;
    let [row @ .., last] = rho else {
        return Err("batched frontend row weights".into());
    };
    if row.len() != b.len() {
        return Err("batched frontend row weights".into());
    }
    let mut weights = vec![f.zero(); input.weights.len()];
    let mut constant = blas::dot(row, &b, f);
    for term in a {
        f.fma(&mut weights[term.w], &row[term.c], &term.k);
    }
    f.add(&mut constant, &f.mulf(last, &input.target));
    blas::axpy(&mut weights, &f.neg(last), &input.weights, f);
    let target = f.neg(&constant);
    Ok(LinearClaim { weights, target })
}

#[cfg(test)]
mod tests;
