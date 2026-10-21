// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

use crate::proof::{LayerProof, RoundPoly, SumcheckProof, SumcheckProofGeometry};
use runtime_algebra::{ElementOf, RuntimeField, SupportsSampling};
use runtime_random::RandomEngine;

pub fn sample<
    const W: usize,
    F: RuntimeField<W> + SupportsSampling<W> + core_algebra::SerializableField,
    R: RandomEngine,
>(
    geometry: &SumcheckProofGeometry,
    rng: &mut R,
    f: &F,
) -> (SumcheckProof<W, F>, Vec<ElementOf<F>>) {
    let layout = geometry.pad_layout(0);
    let mut witness = Vec::with_capacity(layout.size);
    let mut layers = Vec::with_capacity(layout.layers.len());
    for layer in &layout.layers {
        let mut rounds = Vec::with_capacity(layer.rounds.len());
        for pair in &layer.rounds {
            assert_eq!(witness.len(), pair[0]);
            let evaluations = [rng.elt_field(f), rng.elt_field(f)];
            witness.extend(evaluations.clone());
            rounds.push(RoundPoly { evaluations });
        }
        assert_eq!(witness.len(), layer.claims[0]);
        let claims = [rng.elt_field(f), rng.elt_field(f)];
        witness.extend(claims.clone());
        witness.push(f.mulf(&claims[0], &claims[1]));
        layers.push(LayerProof { rounds, claims });
    }
    (SumcheckProof { layers }, witness)
}
