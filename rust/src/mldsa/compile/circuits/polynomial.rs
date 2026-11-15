// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Polynomial wires used by the binary SampleInBall relation.
use crate::{
    compile::logic::{Eltw, Logic},
    mldsa::proto::N,
};
pub(crate) struct PolynomialW<L: Logic> {
    pub coefficients: [Eltw<L>; N],
}

impl<L: Logic> Clone for PolynomialW<L> {
    fn clone(&self) -> Self {
        Self {
            coefficients: self.coefficients.clone(),
        }
    }
}

impl<L: crate::compile::logic::LogicIO> PolynomialW<L> {
    pub(crate) fn input(logic: &L, pos: &mut usize) -> Self {
        Self {
            coefficients: std::array::from_fn(|_| logic.next(pos)),
        }
    }
}
