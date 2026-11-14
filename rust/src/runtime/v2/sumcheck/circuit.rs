// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Circuit sources for the shared sumcheck engine. Every circuit carries its
//! bound identity.
use crate::core::{
    algebra::SerializableField,
    proto::v2::{Circuit, RawCircuit},
};

pub(crate) trait CircuitSource<F: SerializableField> {
    fn raw(&self) -> &RawCircuit<F>;
    fn source_id(&self) -> &[u8; 32];
}
impl<F: SerializableField> CircuitSource<F> for Circuit<F> {
    fn raw(&self) -> &RawCircuit<F> {
        &self.raw
    }
    fn source_id(&self) -> &[u8; 32] {
        &self.id
    }
}
impl<F: SerializableField, T: CircuitSource<F> + ?Sized> CircuitSource<F> for &T {
    fn raw(&self) -> &RawCircuit<F> {
        (*self).raw()
    }
    fn source_id(&self) -> &[u8; 32] {
        (*self).source_id()
    }
}
