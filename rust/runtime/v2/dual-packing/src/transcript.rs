// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
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
    statement: &[u8],
    inputs: usize,
    auxiliary: usize,
    ts: &mut TranscriptRef<'_>,
) where
    X::Ambient: SerializableField,
{
    if p.binary128_profile() {
        ts.bind(|w| {
            w.write_bytes(b"longfellow/dual-packing128/trace-zero/v1");
            w.write_bytes(statement);
        });
        ts.bind(|w| w.write_bytes(&super::PACKING_BASIS_ID.to_le_bytes()));
    } else {
        ts.bind(|w| {
            w.write_bytes(b"longfellow/dual-packing/generic/trace-zero/v1");
            w.write_bytes(&p.descriptor());
        });
        ts.bind(|w| w.write_bytes(statement));
    }
    // The caller identifies the source with arbitrary, canonically framed
    // bytes (possibly empty). ZK derives the coefficients and affine RHS from
    // earlier messages and challenges on this same transcript. Reabsorbing
    // those values would repeat a linear-size deterministic computation.
    // Keep the public cell counts, field/basis profile and statement binding.
    ts.bind(|w| {
        w.write_bytes(&(inputs as u64).to_le_bytes());
        w.write_bytes(&(auxiliary as u64).to_le_bytes());
    });
}
pub(super) fn challenges<X: PackingExtension>(
    p: &PackingParameters<X>,
    u: &[E<X>],
    ts: &mut TranscriptRef<'_>,
) -> Vec<E<X>>
where
    X::Ambient: SerializableField,
{
    ts.round(crate::runtime::v2::proto::RoundLabel::Packing, |mut w| {
        w.write_elt_field_slice(u, p.field());
        let mut r = w.begin_squeeze();
        let value = (0..p.degree())
            .map(|_| p.field().sample(|n| r.bytes(n)))
            .collect();
        r.end_round(value)
    })
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
