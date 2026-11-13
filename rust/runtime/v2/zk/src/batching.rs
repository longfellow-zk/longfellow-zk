// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Batch the complete masked sumcheck rows into one authenticated linear claim.
//!
//! Fresh independent weights cover every layer equation and the final input
//! equation. All masked messages precede this round; the resulting claim is
//! reconstructed locally by both parties; derived coefficients are not absorbed.
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        v2::{
            sumcheck::{self, symbolic::Constraints},
            transcript::TranscriptRef,
        },
    },
};

mod transcript;

pub struct LinearClaim<E> {
    pub weights: Vec<E>,
    pub target: E,
}

pub(crate) fn batch<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    circuit: &Circuit<F>,
    public: &[F::E],
    constraints: Constraints<F::E>,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<LinearClaim<F::E>, String> {
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
    if constraints.layers.len() != geometry.logw_layers.len() {
        return Err("batched frontend layer count".into());
    }
    let count = private
        .checked_add(geometry.pad_count()?)
        .ok_or("batched frontend layout overflow")?;
    let pads = geometry.pad_layout(private);
    let (a, b) = super::constraint_compiler::compile_layers(&constraints, &pads)?;
    let rho = transcript::coefficients(b.len() + 1, transcript, f);
    let mut weights = vec![f.zero(); count];
    let mut constant = blas::dot(&rho[..b.len()], &b, f);
    for term in a {
        f.fma(&mut weights[term.w], &rho[term.c], &term.k);
    }
    let last = &rho[b.len()];
    let input_constant = f.subf(
        &constraints.input_claim.constant,
        &crate::runtime::algebra::blas::dot(&constraints.input_weights[..public.len()], public, f),
    );
    f.add(&mut constant, &f.mulf(last, &input_constant));
    blas::axpy(
        &mut weights[..private],
        &f.neg(last),
        &constraints.input_weights[public.len()..],
        f,
    );
    for (pad, coefficient) in constraints.input_claim.terms {
        let j = super::constraint_compiler::pad_coordinate(pad, &pads)?;
        f.add(&mut weights[j], &f.mulf(last, &coefficient));
    }
    let target = f.neg(&constant);
    Ok(LinearClaim { weights, target })
}

#[cfg(test)]
#[path = "../tests/batching.rs"]
mod tests;
