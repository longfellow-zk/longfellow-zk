// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{MlDsaParams, N};

/// Native input order: shifted z, raw high/low parts, challenge signs,
/// expanded matrix and encoded t1. Each word is linked to these binary bits.
pub(crate) fn shared_widths<P: MlDsaParams>() -> Vec<usize> {
    let mut widths = vec![P::Z_BITS; P::L * N];
    widths.extend(vec![P::R1_BITS; P::K * N]);
    widths.extend(vec![P::r0_bits(); P::K * N]);
    widths.extend(vec![1; 2 * N]);
    widths.extend(vec![23; P::K * P::L * N]);
    widths.extend(vec![10; P::K * N]);
    widths
}
