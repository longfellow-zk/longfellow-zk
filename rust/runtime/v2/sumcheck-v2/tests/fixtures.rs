// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

impl<T> SplitStream<T> {
    pub(super) fn num_terms<const N: usize>(&self, runs: &Runs<'_, N>) -> usize {
        if self.records.is_empty() {
            0
        } else {
            runs.tokens
                .iter()
                .map(|&i| self.ranges[i as usize].len())
                .sum()
        }
    }
}

impl<'a> SplitLayer<'a> {
    // Compatibility helper for hand-written tests with the former table ordering.
    pub(crate) fn new(layer: &'a Layer) -> Self {
        let max = layer
            .quadratic
            .deltas
            .iter()
            .map(|t| t.k)
            .chain(layer.linear.deltas.iter().map(|t| t.k))
            .chain(layer.constant.deltas.iter().map(|t| t.k))
            .max()
            .unwrap_or(0) as usize;
        let mut classes = vec![CoefficientClass::General; max + 3];
        classes[0] = CoefficientClass::Zero;
        classes[1] = CoefficientClass::One;
        classes[2] = CoefficientClass::MinusOne;
        Self::with_classes(layer, &classes)
    }
}
