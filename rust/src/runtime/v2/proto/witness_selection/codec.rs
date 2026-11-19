// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The decoding of a fingerprint response, which every proof role runs.
use super::{super::read_field, FingerprintResponse};
use crate::core::algebra::SerializableField;

impl<E> FingerprintResponse<E> {
    /// A component reader, called only by the complete readers (proto I2).
    pub(crate) fn read<F: SerializableField<E = E>>(
        input: &mut &[u8],
        f: &F,
    ) -> std::io::Result<Self> {
        Ok(Self {
            values: [read_field(input, f)?, read_field(input, f)?],
        })
    }
}
