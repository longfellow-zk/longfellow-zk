// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{compile::algebra::p256::P256Field, core::proto::v2::Circuit};

/// Compile the MAC-free NEXT predicate without selecting proof parameters.
pub fn generate_sig_circuit(f: &P256Field) -> Result<Circuit<P256Field>, String> {
    Ok(super::adapter::native_circuit(f))
}
