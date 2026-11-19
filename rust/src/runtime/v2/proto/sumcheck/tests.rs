// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::SumcheckProofGeometry;

impl SumcheckProofGeometry {
    /// Every field: the round count of each layer. The pattern is
    /// exhaustive, so a new field does not compile until the statement tests
    /// cover it.
    pub(crate) fn fields_for_test(&self) -> &[usize] {
        let Self { logw_layers } = self;
        logw_layers
    }
}
