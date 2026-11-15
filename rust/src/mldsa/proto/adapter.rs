// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! ML-DSA's use of the exact-mode adapter of the foreign storage layer.
//!
//! The public-key claims are six uniform row projections of the arithmetic
//! modulo q; the hidden-key claim is the batched claim of the sextic frontend.
//! Both read binary words of the signature witness. The adapter itself is
//! `runtime::v2::foreign::adapter::exact`.
use crate::mldsa::proto::{MlDsaParams, N};

/// Six claims modulo q: the coordinates of one claim over F_q^6.
pub const CLAIMS: usize = 6;
/// Quotient width of the public-key instance. Each quotient is below half the
/// number of source bits, at most 61,440 for ML-DSA-65.
pub const PUBLIC_QUOTIENT_BITS: usize = 15;
/// Quotient width of the hidden-key instance: it covers half of 2^19 bits.
pub const HIDDEN_QUOTIENT_BITS: usize = 18;

/// Source words of the public-key claims: shifted z, raw high bits, low bits
/// and the challenge's positive and negative sign bits.
pub fn public_widths<P: MlDsaParams>() -> Vec<usize> {
    let mut widths = vec![P::Z_BITS; P::L * N];
    widths.extend(vec![P::R1_BITS; P::K * N]);
    widths.extend(vec![P::r0_bits(); P::K * N]);
    widths.extend(vec![1; 2 * N]);
    widths
}
