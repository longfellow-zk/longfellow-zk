// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::mldsa::proto::{shared_widths, MlDsaParams, RoutingPlan, N};
pub(crate) const fn key_bits<P: MlDsaParams>() -> usize {
    P::K * P::L * N * 23 + P::K * N * 10
}
pub(crate) const fn native_words<P: MlDsaParams>() -> usize {
    (P::K + P::L + 1) * N
}
pub(crate) fn native_inputs<P: MlDsaParams>() -> usize {
    shared_widths::<P>().len() + native_words::<P>()
}

impl RoutingPlan {
    pub(crate) fn control_count(&self) -> usize {
        self.active.iter().filter(|&&live| live).count()
    }
}
