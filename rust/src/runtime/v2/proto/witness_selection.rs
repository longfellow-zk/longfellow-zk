// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Masked fingerprint responses; coefficients are derived from the transcript.
use crate::core::algebra::SerializableField;

cfg_role! {
    mod codec;
}

pub const FINGERPRINTS: usize = 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FingerprintResponse<E> {
    pub values: [E; FINGERPRINTS],
}
impl<E> FingerprintResponse<E> {
    pub fn write<F: SerializableField<E = E>>(&self, out: &mut Vec<u8>, f: &F) {
        for value in &self.values {
            super::util::write_elt_field(out, value, f);
        }
    }
}
