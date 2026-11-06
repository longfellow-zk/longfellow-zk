// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Masked fingerprint responses; coefficients are derived from the transcript.
use crate::core::algebra::SerializableField;

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
    pub fn read<F: SerializableField<E = E>>(input: &mut &[u8], f: &F) -> std::io::Result<Self> {
        let mut read = || {
            let before = *input;
            let value = super::util::read_elt_field(input, f)?;
            if f.to_bytes(&value) != before[..f.serialized_size_bytes()] {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "noncanonical fingerprint response",
                ));
            }
            Ok(value)
        };
        Ok(Self {
            values: [read()?, read()?],
        })
    }
}
