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
//! Zero outputs receive fresh assertion coefficients at their own layer: the
//! caller's top weights for the first, the preceding combine answer after.
//! Only the current stage's split metadata is retained.
//!
//! This derives affine constraints, not an acceptance decision. The caller must
//! authenticate every stage equation and the final shared-input claim against
//! the commitment received before sumcheck.
use super::{
    circuit::CircuitSource,
    fragments::{self, Schedule, SplitFragment},
    symbolic::{build_constraints, Constraints, LayerChallenges},
    transcript::{end_layer, round_challenge, terminal_challenge},
};
use crate::{
    core::algebra::RegisteredField,
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{proto::sumcheck::SumcheckProof, transcript::TranscriptRef},
    },
};

/// Single-circuit convenience for tests; production callers pass circuit lists.
#[cfg(test)]
pub(crate) fn derive_constraints<
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
>(
    circuit: &crate::core::proto::v2::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<Constraints<F::E>, String> {
    derive_constraints_for_circuits(&[circuit], proof, t, f)
}

/// Validate all message counts before advancing the transcript. Circuit metadata
/// is trusted, as in the single-circuit entry point; shared public inputs must
/// already have been bound by the caller. The top weights are drawn here,
/// before the first message.
pub(crate) fn derive_constraints_for_circuits<
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
>(
    circuits: &[impl CircuitSource<F>],
    proof: &SumcheckProof<W, F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<Constraints<F::E>, String> {
    let schedule = Schedule::new(circuits, f)?;
    proof
        .validate(&schedule.geometry)
        .map_err(|e| e.to_string())?;
    // Draw the top weights before the first message (transcript I8).
    let mut entering = schedule.draw_top(circuits, t, f);
    let mut input_assertions = Vec::new();
    let mut weights = Vec::new();
    if schedule.layers.is_empty() {
        weights = std::mem::take(&mut entering.outputs);
    }
    let mut challenges = Vec::with_capacity(proof.layers.len());
    for (stage, p) in proof.layers.iter().enumerate() {
        let layout = &schedule.layers[stage];
        // Only sparse fragment metadata is local; all dense arrays are global.
        let mut active: Vec<_> = layout
            .fragments
            .iter()
            .map(|s| SplitFragment::new(s, schedule.split(circuits, s)))
            .collect();
        schedule.enter(
            stage,
            std::mem::take(&mut entering),
            &mut weights,
            &mut active,
        );
        let point_l: Vec<_> = p.rounds.iter().map(|m| round_challenge(m, t, f)).collect();
        let terminal = terminal_challenge(&p.cross, t, f);
        let alpha = end_layer(&p.claims, t, f, |r| {
            schedule.after_combine(stage, circuits, r, f, &mut entering, &mut input_assertions)
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
    schedule.finish_inputs(&mut weights, input_assertions, f);
    Ok(build_constraints(proof, challenges, weights, f))
}
