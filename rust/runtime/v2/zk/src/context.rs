// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Shared field/domain references and deterministic layout derivation for v2.
//!
//! The caller supplies an interpolation domain with a stable ordered point set.
//! The prover and verifier use that same domain and field. Circuit metadata
//! determines the witness and pad layout passed to Polygero.
use crate::runtime::algebra::{EvaluationDomain, ZkField};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::{
    core::proto::v2::Circuit,
    runtime::v2::{
        polygero::{PolygeroConfig, PolygeroParam},
        zk::{
            packing_commitment::{PackingCommitment, PackingLayout},
            CircuitGeometry,
        },
    },
};

/// Borrow an interpolation domain together with its own arithmetic field.
pub struct ZkContext<'a, const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>> {
    pub(crate) domain: &'a D,
    _field: std::marker::PhantomData<&'a F>,
}
impl<'a, const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>> ZkContext<'a, W, F, D> {
    pub fn new(domain: &'a D) -> Self {
        Self {
            domain,
            _field: std::marker::PhantomData,
        }
    }
    pub fn field(&self) -> &'a F {
        self.domain.field()
    }
}

/// Count private inputs from the trusted circuit metadata.
#[cfg(any(test, feature = "prover"))]
pub(super) fn private_input_count<F: crate::core::algebra::SerializableField>(
    circuit: &Circuit<F>,
) -> usize {
    assert!(
        circuit.raw.ninput >= circuit.raw.npublic_input,
        "public input count exceeds total inputs"
    );
    circuit.raw.ninput - circuit.raw.npublic_input
}

/// Derive the common source layout and one input-aligned sumcheck pad suffix.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) fn prepare_circuit_layout<
    const W: usize,
    F: ZkField<W> + crate::runtime::algebra::PackingField,
    D: EvaluationDomain<W, F>,
    X: crate::runtime::algebra::PackingExtension<Ambient = F>,
>(
    circuit: &Circuit<F>,
    others: &[&Circuit<F>],
    virtual_inputs: usize,
    config: PolygeroConfig,
    extension: X,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<(CircuitGeometry, PolygeroParam, PackingCommitment<F, X>), String> {
    if ctx.field().is_binary() && !extension.binary128_profile() {
        return Err("binary circuits require the authenticated bit-input packing profile".into());
    }
    let mut circuits = vec![circuit];
    circuits.extend_from_slice(others);
    let private_inputs = InputLayout::new(&circuits, virtual_inputs)?.committed();
    let sc_geom = crate::runtime::v2::sumcheck::circuit_geometry(&circuits)?;
    let layout = PackingLayout::new(private_inputs, sc_geom.pad_count()?, extension.degree())?;
    let param = super::joint::prepare_parameter(layout.witness_count, config, ctx.domain)?;
    // Keep the selected field's identity, mask-cell and backend/domain checks
    // even when this circuit will join a larger participant list.
    let selected = super::joint::SelectedField::from_parameter(
        param.clone(),
        ctx.domain,
        ctx.field().packing_id(),
    )?;
    let geometry = CircuitGeometry {
        sc_geom,
        com_geom: selected.geometry(),
        packing_degree: layout.degree,
    };
    let backend = PackingCommitment::new(ctx.field().clone(), layout, extension)?;
    Ok((geometry, param, backend))
}

/// The shared input array of a participant's components:
/// `[public | committed private | virtual]`.
///
/// Its width is the largest component width. Virtual entries are neither public
/// nor committed: each proof defines them as affine functions of committed
/// inputs, and constraint compilation substitutes those definitions. The
/// primary circuit must end before the virtual suffix, so it cannot read it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InputLayout {
    pub npublic: usize,
    pub committed_end: usize,
    pub ninput: usize,
}
impl InputLayout {
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn new<F: crate::core::algebra::SerializableField>(
        circuits: &[&Circuit<F>],
        virtual_inputs: usize,
    ) -> Result<Self, String> {
        let primary = circuits.first().ok_or("empty circuit list")?;
        let npublic = primary.raw.npublic_input;
        let ninput = circuits.iter().map(|c| c.raw.ninput).max().unwrap();
        if npublic > primary.raw.ninput {
            return Err("public prefix".into());
        }
        let committed_end = ninput
            .checked_sub(virtual_inputs)
            .filter(|&end| end >= npublic)
            .ok_or("virtual input suffix overlaps the public prefix")?;
        if primary.raw.ninput > committed_end
            || circuits.iter().any(|c| c.raw.npublic_input != npublic)
        {
            return Err("primary circuit reads the virtual input suffix".into());
        }
        Ok(Self {
            npublic,
            committed_end,
            ninput,
        })
    }
    pub fn committed(&self) -> usize {
        self.committed_end - self.npublic
    }
    pub fn virtual_count(&self) -> usize {
        self.ninput - self.committed_end
    }
}

/// One virtual input entry: `constant + coefficient * input[source]`, where
/// `source` is an absolute index into the committed private inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirtualInput<E> {
    pub source: usize,
    pub constant: E,
    pub coefficient: E,
}

/// Per-proof definitions of a participant's virtual input suffix, in order.
/// Both roles derive them from the transcript; they are never absorbed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirtualInputs<E> {
    pub entries: Vec<VirtualInput<E>>,
}
impl<E> VirtualInputs<E> {
    pub fn none() -> Self {
        Self {
            entries: Vec::new(),
        }
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn validate(&self, layout: &InputLayout) -> Result<(), String> {
        if self.entries.len() != layout.virtual_count()
            || self
                .entries
                .iter()
                .any(|v| v.source < layout.npublic || v.source >= layout.committed_end)
        {
            return Err("virtual input definitions do not match the layout".into());
        }
        Ok(())
    }
}

/// Binary circuit inputs are bool; degree-one prime inputs are field elements.
pub type CircuitInput<F> = crate::runtime::algebra::packing::BaseElement<
    <F as crate::runtime::algebra::PackingField>::Packing,
>;
