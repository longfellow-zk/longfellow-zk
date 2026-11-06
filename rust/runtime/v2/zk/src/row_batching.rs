// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Batch the complete masked sumcheck rows into one authenticated linear claim.
//!
//! Fresh independent weights cover every layer equation and the final input
//! equation. All masked messages precede this round; the resulting claim is
//! bound before the cross-field adapter samples its rescaling challenge.
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        v2::{
            sumcheck::{self, symbolic::Constraints},
            transcript::Transcript,
        },
    },
};

mod transcript;

pub(crate) struct LinearClaim<E> {
    pub weights: Vec<E>,
    pub target: E,
}

pub(super) fn batch<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    circuit: &Circuit<F>,
    public: &[F::E],
    constraints: Constraints<F::E>,
    transcript: &mut Transcript,
    f: &F,
) -> Result<LinearClaim<F::E>, String> {
    let private = circuit
        .raw
        .ninput
        .checked_sub(circuit.raw.npublic_input)
        .ok_or("prime public prefix")?;
    if public.len() != circuit.raw.npublic_input
        || constraints.input_weights.len() != circuit.raw.ninput
    {
        return Err("prime frontend input shape".into());
    }
    let geometry = sumcheck::circuit_geometry(&[circuit])?;
    if constraints.layers.len() != geometry.logw_layers.len() {
        return Err("prime layer count".into());
    }
    let count = private
        .checked_add(geometry.pad_count()?)
        .ok_or("prime layout overflow")?;
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
    transcript::bind_claim(&weights, &target, transcript, f);
    Ok(LinearClaim { weights, target })
}
