// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
/// 3138 signature values give 768 + (3138-768)*256 = 607488 bits.
/// Twenty is the smallest quotient width covering the canonical layout.
/// The affine ERS variant retains this same quotient width and codec.
pub(super) const QUOTIENT_BITS: usize = 20;
