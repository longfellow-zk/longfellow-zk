// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V1-only compact-row randomness.
use crate::runtime::{algebra::SubfieldV1, random::RandomEngine};

pub trait RandomEngineV1: RandomEngine {
    /// Generates a random subfield element.
    fn elt_subfield_v1<SF: SubfieldV1>(&mut self, sf: &SF) -> SF::E {
        sf.sample(|len| self.bytes(len))
    }

    /// Generates a slice of subfield elements with random values.
    fn elt_subfield_v1_slice<SF: SubfieldV1>(&mut self, len: usize, sf: &SF) -> Vec<SF::E> {
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(self.elt_subfield_v1(sf));
        }
        v
    }
}
impl<R: RandomEngine + ?Sized> RandomEngineV1 for R {}
