// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{algebra::RuntimeField, v2::proto::sumcheck::LayerProof};

#[must_use = "Authenticate terminal and input claims against the original commitment"]
pub(crate) struct Reduction {
    pub messages: LayerProof<Gf2_128Field>,
    pub challenges: Challenges,
}

impl NativeRow {
    pub(crate) fn evaluate(&self, cells: &[Gf2_128]) -> Result<Gf2_128, String> {
        let f = Gf2_128Field::new();
        let mut x = self.constant;
        for (i, k) in &self.terms {
            f.fma(&mut x, k, cells.get(*i).ok_or("SIMD equation index")?);
        }
        Ok(x)
    }
}
