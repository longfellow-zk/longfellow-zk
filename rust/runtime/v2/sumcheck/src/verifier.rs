// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Reconstruct ordinary sumcheck over a circuit described by sparse quad fragments.
//!
//! The wire arrays are global: common inputs at the bottom and concatenated
//! intermediate wires above. Quad fragment offsets affect sparse tensor traversal,
//! not the sumcheck rounds or terminal algebra. At point u, each fragment reads
//! the corresponding slice of one monomial array m(u). Accumulate all public
//! contractions into one q_r, then form a_next=m(u)+alpha*q_r with one BLAS call.
//!
//! The terminal factors are A=<m(u),W> and B=<q_r,W>+L(u), so subtract alpha*L(u)
//! when combining them. Constants K are removed before the rounds; linear terms
//! and assertions use the same path in every fragment. No witness values are
//! needed to derive these public corrections or the final input weights.
//!
//! Each round message precedes its challenge. The cross message precedes the
//! nonzero terminal scale, and both masked factors precede the single alpha.
//! Zero outputs receive fresh assertion coefficients at their own layer.
//! Only the current stage's split metadata is retained.
//!
//! This derives affine constraints, not an acceptance decision. The caller must
//! authenticate every stage equation and the final shared-input claim against
//! the commitment received before sumcheck.
use super::{
    fragments::{self, Schedule, SplitFragment},
    split::SplitLayer,
    symbolic::{build_constraints, Constraints, LayerChallenges},
    transcript::{end_layer, round_challenge, terminal_challenge},
    SumcheckProof,
};
use crate::{
    core::{
        algebra::SerializableField,
        proto::v2::{classify_constants, Circuit},
    },
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::transcript::TranscriptRef,
    },
};

pub(crate) fn derive_constraints<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    circuit: &Circuit<F>,
    proof: &SumcheckProof<W, F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<Constraints<F::E>, String> {
    derive_constraints_for_circuits(&[circuit], proof, t, f)
}

/// Validate all message counts before advancing the transcript. Circuit metadata
/// is trusted, as in the single-circuit entry point; shared public inputs must
/// already have been bound by the caller.
pub(crate) fn derive_constraints_for_circuits<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    circuits: &[&Circuit<F>],
    proof: &SumcheckProof<W, F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<Constraints<F::E>, String> {
    let schedule = Schedule::new(circuits)?;
    proof
        .validate(&schedule.geometry)
        .map_err(|e| e.to_string())?;
    let classes: Vec<_> = circuits
        .iter()
        .map(|c| classify_constants(f, &c.raw.constants))
        .collect();
    schedule.bind(circuits, t);
    let mut input_assertions = Vec::new();
    let mut weights = Vec::new();
    let mut challenges = Vec::with_capacity(proof.layers.len());
    for (stage, p) in proof.layers.iter().enumerate() {
        let layout = &schedule.layers[stage];
        // Only sparse fragment metadata is local; all dense arrays are global.
        let mut active: Vec<_> = layout
            .fragments
            .iter()
            .map(|s| {
                SplitFragment::new(
                    s,
                    SplitLayer::with_classes(
                        &circuits[s.circuit].raw.layers[s.layer],
                        &classes[s.circuit],
                    ),
                )
            })
            .collect();
        schedule.start_layer(&mut weights, &mut active, stage, t, f);
        let point_l: Vec<_> = p.rounds.iter().map(|m| round_challenge(m, t, f)).collect();
        let terminal = terminal_challenge(&p.cross, t, f);
        let alpha = end_layer(&p.claims, t, f, |r| {
            if stage + 1 == schedule.layers.len() {
                input_assertions = schedule.input_assertions(circuits, r, f);
            }
        });
        let constant = fragments::constant(circuits, &weights, &active, f);
        let (next_weights, linear) =
            fragments::transition(circuits, &weights, &active, layout.nw, &point_l, &alpha, f);
        weights = next_weights;
        challenges.push(LayerChallenges {
            point_l,
            terminal,
            alpha,
            constant,
            linear,
        });
    }
    schedule.finish_inputs(circuits, &mut weights, input_assertions, t, f);
    Ok(build_constraints(proof, challenges, weights, f))
}
