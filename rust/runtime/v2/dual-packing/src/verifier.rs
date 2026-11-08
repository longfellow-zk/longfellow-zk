// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    generic::*,
    transcript::{begin, challenges, finish},
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::packing::{AmbientElement as E, PackingExtension, PackingParameters},
        v2::transcript::TranscriptRef,
    },
};
/// Check response shape and traces, replay the challenges, and return the
/// equations to authenticate. This function alone does not verify a commitment.
/// `c` must be the claim derived by ZK on this same transcript; `statement`
/// identifies its source without reabsorbing the derived coefficients.
pub(crate) fn reduce<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    statement: &[u8],
    ts: &mut TranscriptRef<'_>,
) -> Result<Vec<FieldEquation<E<X>>>, String>
where
    X::Ambient: SerializableField,
{
    validate_proof(p, c, proof)?;
    if p.degree() == 1 {
        return reconstruct_validated(p, c, proof, &[]);
    }
    let PackingProof::TraceZero { u, a } = proof else {
        unreachable!()
    };
    begin(p, statement, c.weights.len(), c.auxiliary_count, ts);
    let delta = challenges(p, u, ts);
    finish(p, a, ts);
    reconstruct_validated(p, c, proof, &delta)
}
