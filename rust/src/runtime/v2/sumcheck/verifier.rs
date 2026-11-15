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
    split::SplitLayer,
    symbolic::{build_constraints, Constraints, LayerChallenges},
    transcript::{end_layer, round_challenge, terminal_challenge, TopWeights},
};
use crate::{
    core::{algebra::SerializableField, proto::v2::classify_constants},
    runtime::{
        algebra::{RuntimeField, SupportsSampling},
        v2::{
            proto::sumcheck::SumcheckProof,
            transcript::{Challenge, TranscriptRef},
        },
    },
};

/// Single-circuit convenience for tests; production callers pass circuit lists.
#[cfg(test)]
pub(crate) fn derive_constraints<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    circuit: &crate::core::proto::v2::Circuit<F>,
    proof: &SumcheckProof<W, F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<Constraints<F::E>, String> {
    top_and_derive(&[circuit], proof, t, f)
}

/// Test convenience: draw the top weights from `t`, after the caller has
/// bound every circuit statement, then derive the constraints.
#[cfg(test)]
pub(crate) fn top_and_derive<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    circuits: &[impl CircuitSource<F>],
    proof: &SumcheckProof<W, F>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<Constraints<F::E>, String> {
    let top = super::transcript::top_weights(circuits, t, f)?;
    derive_constraints_for_circuits(circuits, proof, top, t, f)
}

/// Validate all message counts before advancing the transcript. Circuit metadata
/// is trusted, as in the single-circuit entry point; shared public inputs must
/// already have been bound by the caller, and `top` drawn after them.
pub(crate) fn derive_constraints_for_circuits<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    circuits: &[impl CircuitSource<F>],
    proof: &SumcheckProof<W, F>,
    top: Challenge<TopWeights<F::E>>,
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> Result<Constraints<F::E>, String> {
    let schedule = Schedule::new(circuits)?;
    proof
        .validate(&schedule.geometry)
        .map_err(|e| e.to_string())?;
    let classes: Vec<_> = circuits
        .iter()
        .map(|c| classify_constants(f, &c.raw().constants))
        .collect();
    // Accept the top weights before the first message (transcript I8).
    let mut entering = schedule.accept_top(top, t)?;
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
            .map(|s| {
                SplitFragment::new(
                    s,
                    SplitLayer::with_classes(
                        &circuits[s.circuit].raw().layers[s.layer],
                        &classes[s.circuit],
                    ),
                )
            })
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
