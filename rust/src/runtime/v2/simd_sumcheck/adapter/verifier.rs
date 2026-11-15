// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
pub(in crate::runtime::v2::simd_sumcheck) fn reduce(
    p: &Parameters,
    claim: &Claim,
    proof: &Proof,
    id: &[u8; 32],
    t: &mut TranscriptRef<'_>,
) -> Result<[Equation; 2], String> {
    validate(claim)?;
    validate_proof(p, proof)?;
    let delta = transcript::challenges(claim, proof, id, t, p.field());
    transcript::finish(proof.a, t, p.field());
    let weights = kernel::verifier::verifier_weights(claim, &delta, p, p.field());
    Ok(equations(p, claim, proof, &delta, weights))
}
