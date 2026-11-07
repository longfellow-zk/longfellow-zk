// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::generic::*;
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{
            packing::{AmbientElement as E, PackingExtension, PackingParameters},
            SupportsSampling,
        },
        v2::transcript::TranscriptRef,
    },
};
pub(super) fn begin<X: PackingExtension>(
    p: &PackingParameters<X>,
    c: &SourceClaim<E<X>>,
    context: &[u8],
    ts: &mut TranscriptRef<'_>,
) where
    X::Ambient: SerializableField,
{
    if p.binary128_profile() {
        ts.bind(|w| {
            w.write_bytes(b"longfellow/dual-packing128/trace-zero/v1");
            w.write_bytes(context);
        });
        ts.bind(|w| w.write_bytes(&super::PACKING_BASIS_ID.to_le_bytes()));
    } else {
        ts.bind(|w| {
            w.write_bytes(b"longfellow/dual-packing/generic/trace-zero/v1");
            w.write_bytes(&p.descriptor());
        });
        ts.bind(|w| w.write_bytes(context));
    }
    let f = p.field();
    ts.bind(|w| {
        w.write_elt_field_slice(&c.weights, f);
        w.write_elt_field(&c.rhs.constant, f);
    });
    ts.bind(|w| {
        w.write_bytes(&(c.auxiliary_count as u64).to_le_bytes());
        w.write_bytes(&(c.rhs.terms.len() as u64).to_le_bytes());
    });
    for (i, k) in &c.rhs.terms {
        ts.bind(|w| {
            w.write_bytes(&(*i as u64).to_le_bytes());
            w.write_elt_field(k, f);
        });
    }
}
pub(super) fn challenges<X: PackingExtension>(
    p: &PackingParameters<X>,
    u: &[E<X>],
    ts: &mut TranscriptRef<'_>,
) -> Vec<E<X>>
where
    X::Ambient: SerializableField,
{
    ts.round(
        crate::runtime::v2::transcript::RoundLabel::Packing,
        |mut w| {
            w.write_elt_field_slice(u, p.field());
            let mut r = w.begin_squeeze();
            let value = (0..p.degree())
                .map(|_| p.field().sample(|n| r.bytes(n)))
                .collect();
            r.end_round(value)
        },
    )
}
pub(super) fn finish<X: PackingExtension>(
    p: &PackingParameters<X>,
    a: &E<X>,
    ts: &mut TranscriptRef<'_>,
) {
    // A may depend on delta, but it must be fixed before the backend samples
    // challenges to authenticate the two resulting linear equations.
    ts.bind(|w| {
        w.write_bytes(if p.binary128_profile() {
            b"trace-zero128/A"
        } else {
            b"trace-zero/A"
        })
    });
    ts.bind(|w| w.write_elt_field(a, p.field()));
}
