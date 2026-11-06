// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    generic::*,
    transcript::{begin, challenges, finish},
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::packing::{AmbientElement as E, PackingExtension, PackingParameters},
        random::transcript_v2::Transcript,
    },
};
/// Check response shape and traces, replay the challenges, and return the
/// equations to authenticate. This function alone does not verify a commitment.
pub fn verify<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    context: &[u8],
    ts: &mut Transcript,
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
    begin(p, c, context, ts);
    let delta = challenges(p, u, ts);
    finish(p, a, ts);
    reconstruct_validated(p, c, proof, &delta)
}
