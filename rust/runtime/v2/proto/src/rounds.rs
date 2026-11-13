// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Domain tags for the Longfellow v2 protocol roles. The transcript itself
//! accepts numeric tags and has no knowledge of these protocols.

#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum RoundLabel {
    // Tag 0 is reserved; circuit outputs join their layer's assertion round.
    Assertions = 1,
    Sumcheck = 2,
    Terminal = 3,
    Combine = 4,
    Packing = 5,
    // Tag 6 was a bind-only placeholder and is reserved.
    Batching = 7,
    Opening = 8,
    // Tags 9-11 belong to the mdoc cross-field adapter. They stay in this one
    // registry so every protocol tag remains unique.
    #[cfg_attr(not(feature = "mdoc"), allow(dead_code))]
    Rescaling = 9,
    #[cfg_attr(not(feature = "mdoc"), allow(dead_code))]
    Conversion = 10,
    #[cfg_attr(not(feature = "mdoc"), allow(dead_code))]
    RowBatching = 11,
    Fingerprint = 12,
}

impl From<RoundLabel> for u8 {
    fn from(label: RoundLabel) -> Self {
        label as u8
    }
}
