// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::random::PrivateRandom;
pub(in crate::runtime::v2::simd_sumcheck) const MASKS: usize = super::super::MASKS;
pub(in crate::runtime::v2::simd_sumcheck) struct Masks {
    pub cells: [E; 129],
}
impl Masks {
    pub(in crate::runtime::v2::simd_sumcheck) fn sample(rng: &mut impl PrivateRandom) -> Self {
        let f = F::new();
        let mut cells = [f.zero(); MASKS];
        for cell in &mut cells[..128] {
            *cell = rng.elt_field(&f);
        }
        cells[128] = f.mulf(&cells[127], &cells[127]);
        Self { cells }
    }
}
pub(in crate::runtime::v2::simd_sumcheck) fn prove(
    p: &Parameters,
    claim: &Claim,
    packed: &[E],
    auxiliary: &[E],
    masks: Masks,
    id: &[u8; 32],
    t: &mut TranscriptRef<'_>,
) -> Result<(Proof, [Equation; 2]), String> {
    if packed.len() != validate(claim)? || auxiliary.len() != claim.auxiliary_count {
        return Err("SIMD adapter witness shape".into());
    }
    let f = p.field();
    let kernel = kernel::prover::Kernel::new(claim, f);
    let target = claim.rhs.evaluate(auxiliary)?;
    let b = kernel.components(claim, packed, p, f);
    let mut coordinates = [f.zero(); 128];
    coordinates[1..].copy_from_slice(&masks.cells[..127]);
    for i in 1..128 {
        f.fma(&mut coordinates[0], &p.basis()[i], &masks.cells[i - 1]);
    }
    let u = std::array::from_fn(|i| {
        f.addf(
            &f.addf(&b[i], &f.mulf(&p.dual()[i], &target)),
            &f.addf(&coordinates[i], &f.mulf(&coordinates[i], &coordinates[i])),
        )
    });
    let mut proof = Proof { u, a: f.zero() };
    validate_proof(p, &proof)?;
    let delta = transcript::challenges(claim, &proof, id, t, f);
    proof.a = masks.cells[127];
    for (d, x) in delta.iter().zip(coordinates) {
        f.fma(&mut proof.a, d, &x);
    }
    transcript::finish(proof.a, t, f);
    let weights = kernel.weights(claim, &delta, p, f);
    let rows = equations(p, claim, &proof, &delta, weights);
    Ok((proof, rows))
}
