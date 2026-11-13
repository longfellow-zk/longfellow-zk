// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Mutable construction and immutable runtime circuits.
use std::ops::Deref;

use super::{Layer, SerializableField};
use crate::core::proto::DigestBytes;

/// Finalized circuit and its identity. All access is read-only, even through
/// `&mut Circuit`. To edit, consume it with [`Circuit::into_raw`] and then
/// [`RawCircuit::into_builder`], and construct a new circuit with a new identity.
///
/// ```compile_fail,E0594
/// use longfellow_zk::core::proto::{v2::Circuit, SerializableField};
/// fn change_id<F: SerializableField>(c: &mut Circuit<F>) {
///     c.id = [0; 32];
/// }
/// ```
/// ```compile_fail,E0596
/// use longfellow_zk::core::proto::{v2::Circuit, SerializableField};
/// fn change_constants<F: SerializableField>(c: &mut Circuit<F>) {
///     c.raw.constants.clear();
/// }
/// ```
/// ```compile_fail,E0596
/// use longfellow_zk::core::proto::{v2::Circuit, SerializableField};
/// fn change_gates<F: SerializableField>(c: &mut Circuit<F>) {
///     c.raw.layers[0].quadratic.tokens.clear();
/// }
/// ```
#[repr(transparent)]
pub struct Circuit<F: SerializableField>(CircuitParts<F>);

/// Read-only field view of a finalized circuit. `Circuit` deliberately does not
/// implement `DerefMut` or expose a mutable reference to these parts.
pub struct CircuitParts<F: SerializableField> {
    pub raw: RawCircuit<F>,
    pub id: DigestBytes,
}

impl<F: SerializableField> Circuit<F> {
    /// Finalize the stored representation by computing its identity. The
    /// compiler keeps a `RawCircuit` until segmentation is complete. Generated
    /// circuits may use the single-run streams produced by `Stream::from_terms`.
    pub fn from_raw(f: &F, raw: RawCircuit<F>) -> Self {
        Self::new(super::compute_id(f, &raw), raw)
    }

    /// The reader has already checked this identity against the stored data.
    pub(super) fn new(id: DigestBytes, raw: RawCircuit<F>) -> Self {
        Self(CircuitParts { raw, id })
    }

    /// Fault injection for tests of transcript binding and forged metadata.
    #[cfg(test)]
    pub(crate) fn with_test_id(id: DigestBytes, raw: RawCircuit<F>) -> Self {
        Self::new(id, raw)
    }

    /// Consume this circuit, discarding the identity before any edits.
    pub fn into_raw(self) -> RawCircuit<F> {
        self.0.raw
    }
}

impl<F: SerializableField> Deref for Circuit<F> {
    type Target = CircuitParts<F>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Finalized circuit without an identity, also used for generated adapter
/// instances. Freezing and field access add no allocation, scan, or checks.
///
/// ```compile_fail,E0596
/// use longfellow_zk::core::proto::{v2::RawCircuit, SerializableField};
/// fn change_layers<F: SerializableField>(c: &mut RawCircuit<F>) {
///     c.layers.clear();
/// }
/// ```
/// ```compile_fail,E0609
/// use longfellow_zk::core::proto::{v2::RawCircuit, SerializableField};
/// fn compiler_output_has_no_id<F: SerializableField>(c: &RawCircuit<F>) {
///     let _ = c.id;
/// }
/// ```
#[repr(transparent)]
pub struct RawCircuit<F: SerializableField>(RawCircuitBuilder<F>);

/// Mutable circuit construction data. Constructors are responsible for valid
/// geometry and assertion counts; any coefficient/stream edits must preserve
/// those counts or rebuild the affected layers with `Layer::with_assertions`.
/// Only the finalized `RawCircuit` can be used by the runtime.
pub struct RawCircuitBuilder<F: SerializableField> {
    pub ninput: usize,
    pub npublic_input: usize,
    pub noutput: usize,
    pub logv: usize,
    pub constants: Vec<F::E>,
    pub layers: Vec<Layer>,
}

impl<F: SerializableField> RawCircuitBuilder<F> {
    /// Transfer ownership into a read-only circuit without changing its data.
    pub fn build(self) -> RawCircuit<F> {
        RawCircuit(self)
    }
}

impl<F: SerializableField> RawCircuit<F> {
    /// Consume the finalized circuit to resume mutable construction.
    pub fn into_builder(self) -> RawCircuitBuilder<F> {
        self.0
    }
}

impl<F: SerializableField> Deref for RawCircuit<F> {
    type Target = RawCircuitBuilder<F>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
