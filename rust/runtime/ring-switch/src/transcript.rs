// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Fix the entire incoming affine claim before beta; fix all messages before gamma.
use super::{BitLinearClaim, RingSwitch128Proof, PACKING_BASIS_ID, RING_MESSAGES};
use crate::runtime::{
    algebra::{
        gf2_128::{Gf2_128 as E, Gf2_128Field as F},
        AlgebraicField,
    },
    random::{RandomEngine, Transcript},
};
pub(super) fn begin(claim: &BitLinearClaim, context: &[u8], ts: &mut Transcript, f: &F) -> E {
    ts.write_bytes(b"longfellow/ring-switch128/flat-trace/v1");
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
    ts.write_bytes(b"flat128/beta/nonzero");
    loop {
        let beta = E::from(ts.u128());
        if !f.is_zero(&beta) {
            return beta;
        }
    }
}
pub(super) fn batch(proof: &RingSwitch128Proof, ts: &mut Transcript, f: &F) -> [E; RING_MESSAGES] {
    ts.write_bytes(b"flat128/entire-response");
    ts.write_elt_field_slice(&proof.messages, f);
    ts.write_bytes(b"flat128/independent-gamma");
    std::array::from_fn(|_| E::from(ts.u128()))
}
