// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The committed-pad positions of a sumcheck proof, which both proof roles
//! address.
use super::{pad_count, SumcheckProofGeometry};

#[derive(Clone, Debug)]
pub(crate) struct LayerPadLayout {
    pub(crate) rounds: Vec<[usize; 2]>,
    pub(crate) claims: [usize; 2],
    pub(crate) product: usize,
    pub(crate) cross: usize,
}
#[derive(Clone, Debug)]
pub(crate) struct CircuitPadLayout {
    pub(crate) layers: Vec<LayerPadLayout>,
}

impl SumcheckProofGeometry {
    pub(crate) fn pad_layout(&self, base: usize) -> CircuitPadLayout {
        base.checked_add(self.pad_count())
            .expect("sumcheck pad layout overflow");
        let layers: Vec<_> = self
            .logw_layers
            .iter()
            .scan(base, |next, &logw| {
                let count = pad_count(logw);
                let start = *next;
                *next += count;
                let terminal = *next - 4;
                let rounds = (0..logw)
                    .map(|round| [start + 2 * round, start + 2 * round + 1])
                    .collect();
                Some(LayerPadLayout {
                    rounds,
                    claims: [terminal, terminal + 1],
                    product: terminal + 2,
                    cross: terminal + 3,
                })
            })
            .collect();
        CircuitPadLayout { layers }
    }
}
