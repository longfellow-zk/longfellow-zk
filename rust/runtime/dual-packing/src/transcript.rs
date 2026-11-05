// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::generic::*;
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{
            packing::{AmbientElement as E, PackingExtension, PackingParameters},
            SupportsSampling,
        },
        random::{RandomEngine, Transcript},
    },
};
pub(super) fn begin<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    context: &[u8],
    ts: &mut Transcript,
) where
    X::Ambient: SerializableField,
{
    if p.binary128_profile() {
        ts.write_bytes(b"longfellow/dual-packing128/trace-zero/v1");
        ts.write_bytes(context);
        ts.write_bytes(&super::PACKING_BASIS_ID.to_le_bytes());
    } else {
        ts.write_bytes(b"longfellow/dual-packing/generic/trace-zero/v1");
        ts.write_bytes(&p.descriptor());
        ts.write_bytes(context);
    }
    let f = p.field();
    ts.write_elt_field_slice(&c.weights, f);
    ts.write_elt_field(&c.rhs.constant, f);
    ts.write_bytes(&(c.auxiliary_count as u64).to_le_bytes());
    ts.write_bytes(&(c.rhs.terms.len() as u64).to_le_bytes());
    for (i, k) in &c.rhs.terms {
        ts.write_bytes(&(*i as u64).to_le_bytes());
        ts.write_elt_field(k, f);
    }
}
pub(super) fn challenges<X: PackingExtension>(
    p: &PackingParameters<X>,
    u: &[E<X>],
    ts: &mut Transcript,
) -> Vec<E<X>>
where
    X::Ambient: SerializableField,
{
    // Bind the entire first response before drawing independent coordinates.
    // Replacing delta by powers of one challenge would change the soundness bound.
    ts.write_bytes(if p.binary128_profile() {
        b"trace-zero128/U"
    } else {
        b"trace-zero/U"
    });
    ts.write_elt_field_slice(u, p.field());
    ts.write_bytes(if p.binary128_profile() {
        b"trace-zero128/independent-delta"
    } else {
        b"trace-zero/independent-delta"
    });
    (0..p.degree())
        .map(|_| p.field().sample(|n| ts.bytes(n)))
        .collect()
}
pub(super) fn finish<X: PackingExtension>(p: &PackingParameters<X>, a: &E<X>, ts: &mut Transcript) {
    // A may depend on delta, but it must be fixed before the backend samples
    // challenges to authenticate the two resulting linear equations.
    ts.write_bytes(if p.binary128_profile() {
        b"trace-zero128/A"
    } else {
        b"trace-zero/A"
    });
    ts.write_elt_field(a, p.field());
}
