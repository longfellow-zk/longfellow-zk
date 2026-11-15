// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::ComposedGeometry;
use crate::runtime::v2::proto::{polygero::PolygeroConfig, zk::CircuitProofGeometry};

impl ComposedGeometry {
    /// Every field, in declaration order: the host and split circuit
    /// geometries and the profile. The pattern is exhaustive, so a new field
    /// does not compile until the statement tests cover it.
    pub(crate) fn fields_for_test(
        &self,
    ) -> (&CircuitProofGeometry, &CircuitProofGeometry, PolygeroConfig) {
        let Self {
            host,
            split,
            config,
        } = self;
        (host, split, *config)
    }
}
