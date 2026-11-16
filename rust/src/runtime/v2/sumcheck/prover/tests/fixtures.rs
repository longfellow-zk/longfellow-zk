// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::super::*;
use crate::{
    core::{algebra::ElementOf, proto::v2::Circuit},
    runtime::v2::transcript::Transcript,
};

/// Diagnostic entry point for tests that supply arbitrary intermediate witnesses.
pub(crate) fn prove_core<F: RuntimeField + RegisteredField + SupportsSampling>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<F>,
    circuit: &Circuit<F>,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> (SumcheckProof<F>, Constraints<ElementOf<F>>) {
    let circuits = [circuit];
    let schedule = Schedule::new(&circuits, f).unwrap();
    let entering = schedule.draw_top(&circuits, transcript, f);
    let layers = schedule.classify_layers(&circuits);
    prove_layers(
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
pub(crate) fn prove<F: RuntimeField + RegisteredField + SupportsSampling>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<F>,
    circuit: &Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<F>, Constraints<ElementOf<F>>) {
    assert!(
        !w_layers.is_empty(),
        "use prove_core for a zero-layer circuit"
    );
    prove_core(w_layers, pads, circuit, &mut transcript.borrow(), f)
}
