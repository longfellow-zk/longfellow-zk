// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CircuitProofGeometry, ZkProofGeometry};
use crate::runtime::v2::proto::{polygero::PolygeroConfig, sumcheck::SumcheckProofGeometry};

impl CircuitProofGeometry {
    /// Every field, in declaration order: the sumcheck geometry, the packing
    /// degree and the committed cell count. The pattern is exhaustive, so a
    /// new field does not compile until the statement tests cover it.
    pub(crate) fn fields_for_test(&self) -> (&SumcheckProofGeometry, usize, usize) {
        let Self {
            sumcheck,
            packing_degree,
            nw,
        } = self;
        (sumcheck, *packing_degree, *nw)
    }
}

impl ZkProofGeometry {
    /// Every field, in declaration order: the circuit geometry and the
    /// profile. The pattern is exhaustive, so a new field does not compile
    /// until the statement tests cover it.
    pub(crate) fn fields_for_test(&self) -> (&CircuitProofGeometry, PolygeroConfig) {
        let Self { circuit, config } = self;
        (circuit, *config)
    }
}
