// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    generic::*,
    transcript::{challenges, finish},
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::packing::{AmbientElement as E, PackingExtension, PackingParameters},
        v2::{proto::dual_packing::PackingProof, transcript::Bound},
    },
};
/// Check response shape and traces, replay the challenges, and return the
/// equations to authenticate. This function alone does not verify a commitment.
/// `c` must be the claim derived by ZK on this same transcript; its derived
/// coefficients are never absorbed.
pub(in crate::runtime::v2) fn reduce<X: PackingExtension>(
    ts: &mut Bound<'_, PackingParameters<X>>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
) -> Result<Vec<FieldEquation<E<X>>>, String>
where
    X::Ambient: SerializableField,
{
    let p = ts.part();
    validate_proof(p, c, proof)?;
    if p.degree() == 1 {
        return reconstruct_validated(p, c, proof, &[]);
    }
    let PackingProof::TraceZero { u, a } = proof else {
        unreachable!()
    };
    let mut session = ts.transcript();
    let delta = challenges(p, u, &mut session);
    finish(p, a, &mut session);
    reconstruct_validated(p, c, proof, &delta)
}
