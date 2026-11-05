// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{compile::algebra::gf2_128::Gf2_128Field, core::proto::v2::Circuit};

/// Compile the MAC-free NEXT predicate without selecting proof parameters.
pub fn generate_hash_circuit(
    f: &Gf2_128Field,
    num_attrs: usize,
) -> Result<Circuit<Gf2_128Field>, String> {
    super::adapter::binary_circuit(f, num_attrs)
}
