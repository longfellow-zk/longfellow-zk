// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Domain tags for the Longfellow v2 protocol roles. The transcript itself
//! accepts numeric tags and has no knowledge of these protocols. A tag labels
//! the round footer of the draw that ends a node; a draw that continues the
//! current stream (transcript I7) writes no footer, so its tag is unused.

#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum RoundLabel {
    // Tag 0 is reserved. A sumcheck's top weights; every later stage's
    // weights extend the preceding combine answer.
    Assertions = 1,
    Sumcheck = 2,
    Terminal = 3,
    Combine = 4,
    Packing = 5,
    // Tag 6 was a bind-only placeholder and is reserved.
    Batching = 7,
    Opening = 8,
    // Tags 9-11 belong to foreign storage: the split challenge `eta` (which
    // extends the split frontend's last answer, so it opens no node), the
    // adapter's conversion challenges, and the row batching of pure-foreign
    // storage. They stay in this one registry so every tag remains unique.
    Rescaling = 9,
    Conversion = 10,
    RowBatching = 11,
    Fingerprint = 12,
}

impl From<RoundLabel> for u8 {
    fn from(label: RoundLabel) -> Self {
        label as u8
    }
}
