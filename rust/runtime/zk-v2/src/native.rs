// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Masked sumcheck without a field-specific commitment backend.
//!
//! This is a reduction, NOT a standalone proof or verifier. Its caller must
//! authenticate every returned linear coefficient against the same pre-challenge
//! witness. In particular, checking only the
//! terminal input claim is insufficient. No native masks are disclosed here.
use crate::{
    core::{algebra::SerializableField, proto::v2::Circuit},
    runtime::{
        algebra::{blas, RuntimeField, SupportsSampling},
        random::{RandomEngine, Transcript},
        sumcheck_v2::{
            self, symbolic::Constraints, SumcheckProof, SumcheckProofGeometry, TranscriptSumcheck,
        },
    },
};

pub(crate) struct LinearClaim<E> {
    pub weights: Vec<E>,
    pub target: E,
}

fn batch<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
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
        .ok_or("native public prefix")?;
    if public.len() != circuit.raw.npublic_input
        || constraints.input_weights.len() != circuit.raw.ninput
    {
        return Err("native frontend input shape".into());
    }
    let geometry = sumcheck_v2::circuit_geometry(&[circuit])?;
    if constraints.layers.len() != geometry.logw_layers.len() {
        return Err("native layer count".into());
    }
    let count = private
        .checked_add(geometry.pad_count()?)
        .ok_or("native layout overflow")?;
    let pads = geometry.pad_layout(private);
    let (a, b) = super::constraint_compiler::compile_layers(&constraints, &pads)?;
    // All masked native messages have already been absorbed before these fresh
    // row weights. Include every layer row AND the final input equation.
    transcript.write_bytes(b"native-masked-sumcheck/all-linear-rows/v1");
    let rho = transcript.elt_field_slice(b.len() + 1, f);
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
    // Explicitly fix the complete adapter statement before its rescaling alpha.
    transcript.write_bytes(b"native-masked-sumcheck/fixed-linear-claim/v1");
    transcript.write_bytes(&(weights.len() as u64).to_le_bytes());
    transcript.write_elt_field_slice(&weights, f);
    transcript.write_elt_field(&target, f);
    Ok(LinearClaim { weights, target })
}

cfg_prover! { #[path="native_prover.rs"] mod prover; pub(crate) use prover::{prepare, prove, Prepared}; }
cfg_verifier! { #[path="native_verifier.rs"] mod verifier; pub(crate) use verifier::reduce; }
