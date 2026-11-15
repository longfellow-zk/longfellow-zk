// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::PackingLayout;

impl PackingLayout {
    /// Every field, in declaration order: private inputs, packed words,
    /// masks, suffix start, pad cells, masks start, witness count, degree.
    /// The pattern is exhaustive, so a new field does not compile until the
    /// statement tests cover it.
    pub(crate) fn fields_for_test(&self) -> [usize; 8] {
        let Self {
            private_inputs,
            packed_words,
            masks,
            suffix_start,
            pad_cells,
            masks_start,
            witness_count,
            degree,
        } = *self;
        [
            private_inputs,
            packed_words,
            masks,
            suffix_start,
            pad_cells,
            masks_start,
            witness_count,
            degree,
        ]
    }
}
