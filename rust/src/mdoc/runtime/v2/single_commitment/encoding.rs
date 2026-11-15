// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
/// Explicit representation of signature coordinates in the binary commitment.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SignatureEncoding {
    /// Every nonshared signature value occupies its canonical 256-bit encoding.
    Canonical,
    /// The named ECDSA ERS values use `x=2*b-8` with a three-bit index b.
    #[default]
    AffineErs,
}
