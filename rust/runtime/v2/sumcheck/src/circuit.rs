// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Circuit sources for the shared sumcheck engine. Independent circuits carry
//! their bound identity; deterministic instances supply only their raw terms.
use crate::core::{
    algebra::SerializableField,
    proto::v2::{Circuit, RawCircuit},
};

/// Raw instances may be used only when their fixed generator/layout is bound
/// and both parties derive all parameters from prior transcript data. Their
/// coefficients must never be rebound through an instance hash.
pub(crate) trait CircuitSource<F: SerializableField> {
    fn raw(&self) -> &RawCircuit<F>;
    fn source_id(&self) -> Option<&[u8; 32]>;
}
impl<F: SerializableField> CircuitSource<F> for Circuit<F> {
    fn raw(&self) -> &RawCircuit<F> {
        &self.raw
    }
    fn source_id(&self) -> Option<&[u8; 32]> {
        Some(&self.id)
    }
}
impl<F: SerializableField> CircuitSource<F> for RawCircuit<F> {
    fn raw(&self) -> &RawCircuit<F> {
        self
    }
    fn source_id(&self) -> Option<&[u8; 32]> {
        None
    }
}
impl<F: SerializableField, T: CircuitSource<F> + ?Sized> CircuitSource<F> for &T {
    fn raw(&self) -> &RawCircuit<F> {
        (*self).raw()
    }
    fn source_id(&self) -> Option<&[u8; 32]> {
        (*self).source_id()
    }
}
