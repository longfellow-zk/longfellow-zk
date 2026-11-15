// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::super::*;
use crate::{
    core::{algebra::ElementOf, proto::v2::Circuit},
    runtime::v2::{sumcheck::top_weights, transcript::Transcript},
};

/// Diagnostic entry point for tests that supply arbitrary intermediate witnesses.
pub(crate) fn prove_core<
    const W: usize,
    F: RuntimeField<W> + RegisteredField + SupportsSampling,
>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<W, F>,
    circuit: &Circuit<F>,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> (SumcheckProof<W, F>, Constraints<ElementOf<F>>) {
    let circuits = [circuit];
    let top = top_weights(&circuits, transcript, f).unwrap();
    let (schedule, entering) = accept_top(top, &circuits, transcript).unwrap();
    let layers = schedule.split_layers(&circuits);
    prove_split(
        &circuits,
        layers,
        w_layers,
        SumcheckPads::from_proof(pads.clone()),
        schedule,
        entering,
        transcript,
        f,
    )
    .unwrap()
}

/// Bind the statement and run the prover for a test with at least one layer.
/// The final entry of w_layers supplies the circuit inputs; zero-layer tests
/// bind the statement explicitly and call prove_core.
pub(crate) fn prove<const W: usize, F: RuntimeField<W> + RegisteredField + SupportsSampling>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<W, F>,
    circuit: &Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, Constraints<ElementOf<F>>) {
    assert!(
        !w_layers.is_empty(),
        "use prove_core for a zero-layer circuit"
    );
    prove_core(w_layers, pads, circuit, &mut transcript.borrow(), f)
}
