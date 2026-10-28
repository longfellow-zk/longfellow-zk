// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Paper's native verifier: public trace checks, followed by two linear equations.
use super::{field::PolynomialBasis128, BitLinearClaim, DualPacking128Proof, PackedLinearClaim};
use crate::runtime::{algebra::gf2_128::Gf2_128Field, random::Transcript};
pub fn reduce(
    basis: &PolynomialBasis128,
    claim: &BitLinearClaim,
    proof: &DualPacking128Proof,
    context: &[u8],
    ts: &mut Transcript,
    f: &Gf2_128Field,
) -> Result<[PackedLinearClaim; 2], String> {
    claim.validate()?;
    super::validate_traces(basis, &proof.u)?;
    super::transcript::begin(claim, context, ts, f);
    let delta = super::transcript::challenge(&proof.u, ts, f);
    super::transcript::finish(proof.a, ts, f);
    Ok(super::reconstruct(basis, claim, proof, &delta, f))
}
