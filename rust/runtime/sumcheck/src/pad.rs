// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

use runtime_random::RandomEngine;

/// Generates a new random sumcheck proof pad for the given geometry.
pub fn sample<
    const W: usize,
    F: runtime_algebra::poly::InterpolationField<W>
        + core_algebra::SerializableField
        + runtime_algebra::SupportsSampling<W>,
    R: RandomEngine,
>(
    geometry: &crate::proof::SumcheckProofGeometry,
    rng: &mut R,
    f: &F,
) -> (crate::proof::SumcheckProof<W, F>, Vec<F::E>) {
    let mut pad = crate::proof::SumcheckProof { layers: Vec::new() };
    let mut witness = Vec::new();

    for &logw in &geometry.logw_layers {
        // Round pads, in round/hand/evaluation order.
        let mut hp = [Vec::with_capacity(logw), Vec::with_capacity(logw)];
        for _round in 0..logw {
            for hp_slot in &mut hp {
                let r0 = rng.elt_field(f);
                let r2 = rng.elt_field(f);
                witness.push(r0.clone());
                witness.push(r2.clone());
                hp_slot.push(runtime_proto::RoundPoly {
                    evaluations: [r0, r2],
                });
            }
        }

        // Endpoint pads.
        let r0 = rng.elt_field(f);
        let r1 = rng.elt_field(f);
        witness.push(r0.clone());
        witness.push(r1.clone());

        // Commit to product of pads for product proof.
        let rr = f.mulf(&r0, &r1);
        witness.push(rr);

        pad.layers.push(crate::LayerProof {
            hp,
            claims: [r0, r1],
        });
    }

    (pad, witness)
}
