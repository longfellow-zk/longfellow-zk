// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{
    generic::*,
    transcript::{begin, challenges, finish},
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::packing::{AmbientElement as E, PackingExtension, PackingParameters},
        v2::transcript::Bound,
    },
};
/// Check response shape and traces, replay the challenges, and return the
/// equations to authenticate. This function alone does not verify a commitment.
/// `c` must be the claim derived by ZK on this same transcript; `statement`
/// identifies its source without reabsorbing the derived coefficients.
pub(in crate::runtime::v2) fn reduce<X: PackingExtension>(
    ts: &mut Bound<'_, PackingParameters<X>>,
    c: &SourceClaim<E<X>>,
    proof: &PackingProof<E<X>>,
    statement: &[u8],
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
    begin(
        p,
        statement,
        c.weights.len(),
        c.auxiliary_count,
        &mut session,
    );
    let delta = challenges(p, u, &mut session);
    finish(p, a, &mut session);
    reconstruct_validated(p, c, proof, &delta)
}
