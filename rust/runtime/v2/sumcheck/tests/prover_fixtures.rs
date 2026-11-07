// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{
    algebra::ElementOf,
    v2::{sumcheck::TranscriptSumcheck, transcript::Transcript},
};

/// Diagnostic entry point for tests that supply arbitrary intermediate witnesses.
pub(crate) fn prove_core<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::v2::Circuit<F>,
    transcript: &mut TranscriptRef<'_>,
    f: &F,
) -> (SumcheckProof<W, F>, Constraints<ElementOf<F>>) {
    let layers = super::super::split::split_layers(circuit, f);
    prove_split(
        &[circuit],
        vec![layers],
        w_layers,
        pads,
        Schedule::new(&[circuit]).unwrap(),
        transcript,
        f,
    )
    .unwrap()
}

/// Bind the statement and run the prover for a test with at least one layer.
/// The final entry of w_layers supplies the circuit inputs; zero-layer tests
/// bind the statement explicitly and call prove_core.
pub(crate) fn prove<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling>(
    w_layers: Vec<Vec<ElementOf<F>>>,
    pads: &SumcheckProof<W, F>,
    circuit: &crate::core::proto::v2::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, Constraints<ElementOf<F>>) {
    let inputs = w_layers
        .last()
        .expect("use prove_core for a zero-layer circuit");
    transcript
        .borrow()
        .write_sumcheck_statement(circuit, &inputs[..circuit.raw.npublic_input], f);
    prove_core(w_layers, pads, circuit, &mut transcript.borrow(), f)
}
