// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Circuit sources for the shared sumcheck engine. The statement holds every
//! circuit's identity (transcript I3); the engine reads only the circuit.
use crate::core::{
    algebra::SerializableField,
    proto::{
        v2::{Circuit, RawCircuit},
        DigestBytes,
    },
};

pub(crate) trait CircuitSource<F: SerializableField> {
    fn raw(&self) -> &RawCircuit<F>;
    /// The circuit ID, which names its content.
    fn id(&self) -> &DigestBytes;
}
impl<F: SerializableField> CircuitSource<F> for Circuit<F> {
    fn raw(&self) -> &RawCircuit<F> {
        &self.raw
    }
    fn id(&self) -> &DigestBytes {
        &self.id
    }
}
impl<F: SerializableField, T: CircuitSource<F> + ?Sized> CircuitSource<F> for &T {
    fn raw(&self) -> &RawCircuit<F> {
        (*self).raw()
    }
    fn id(&self) -> &DigestBytes {
        (*self).id()
    }
}
