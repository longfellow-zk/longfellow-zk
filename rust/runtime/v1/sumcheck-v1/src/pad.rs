// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Sample the additive pads in the legacy commitment and wire order.
//!
//! Within each layer, visit round, then hand, then the two transmitted polynomial
//! evaluations. Finally sample the two witness-claim pads and append their
//! product to the committed vector. Return both the structured pad messages and
//! the flattened witness suffix consumed by the ZK commitment.
use crate::runtime::random::RandomEngine;

/// Generates a new random sumcheck proof pad for the given geometry.
pub fn sample<
    const W: usize,
    F: crate::runtime::algebra::poly::InterpolationField<W>
        + crate::core::algebra::SerializableField
        + crate::runtime::algebra::SupportsSampling,
    R: RandomEngine,
>(
    geometry: &crate::runtime::sumcheck_v1::proof::SumcheckProofGeometry,
    rng: &mut R,
    f: &F,
) -> (
    crate::runtime::sumcheck_v1::proof::SumcheckProof<W, F>,
    Vec<F::E>,
) {
    let mut pad = crate::runtime::sumcheck_v1::proof::SumcheckProof { layers: Vec::new() };
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
                hp_slot.push(crate::runtime::proto::sumcheck_v1::RoundPoly {
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

        pad.layers.push(crate::runtime::sumcheck_v1::LayerProof {
            hp,
            claims: [r0, r1],
        });
    }

    (pad, witness)
}
