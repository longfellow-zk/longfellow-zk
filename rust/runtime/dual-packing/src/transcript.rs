// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Bind the claim, then U before independent delta coordinates, then response A.
use super::{BitLinearClaim, DUAL_PACKING_COORDINATES, PACKING_BASIS_ID};
use crate::runtime::{
    algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as F},
    random::{RandomEngine, Transcript},
};
pub(super) fn begin(claim: &BitLinearClaim, context: &[u8], ts: &mut Transcript, f: &F) {
    ts.write_bytes(b"longfellow/dual-packing128/trace-zero/v1");
    ts.write_bytes(context);
    ts.write_bytes(&PACKING_BASIS_ID.to_le_bytes());
    ts.write_elt_field_slice(&claim.weights, f);
    ts.write_elt_field(&claim.rhs.constant, f);
    ts.write_bytes(&(claim.auxiliary_count as u64).to_le_bytes());
    ts.write_bytes(&(claim.rhs.terms.len() as u64).to_le_bytes());
    for &(index, coefficient) in &claim.rhs.terms {
        ts.write_bytes(&(index as u64).to_le_bytes());
        ts.write_elt_field(&coefficient, f);
    }
}
pub(super) fn challenge(
    u: &[E; DUAL_PACKING_COORDINATES],
    ts: &mut Transcript,
    f: &F,
) -> [E; DUAL_PACKING_COORDINATES] {
    ts.write_bytes(b"trace-zero128/U");
    ts.write_elt_field_slice(u, f);
    ts.write_bytes(b"trace-zero128/independent-delta");
    std::array::from_fn(|_| E::from(ts.u128()))
}
pub(super) fn finish(a: E, ts: &mut Transcript, f: &F) {
    ts.write_bytes(b"trace-zero128/A");
    ts.write_elt_field(&a, f);
}
