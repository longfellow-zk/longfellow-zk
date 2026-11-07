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
        proto::zk::PackingLayout,
        zk::{packing_commitment::PackingCommitment, CircuitGeometry},
    },
};

/// Borrow an interpolation domain together with its own arithmetic field.
pub struct ZkContext<'a, const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>> {
    pub domain: &'a D,
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
    config: PolygeroConfig,
    extension: X,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<(CircuitGeometry, PolygeroParam, PackingCommitment<F, X>), String> {
    if ctx.field().is_binary() && !extension.binary128_profile() {
        return Err("binary circuits require the authenticated bit-input packing profile".into());
    }
    let private_inputs = circuit
        .raw
        .ninput
        .checked_sub(circuit.raw.npublic_input)
        .ok_or("public prefix")?;
    let mut circuits = vec![circuit];
    circuits.extend_from_slice(others);
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

/// Binary circuit inputs are bool; degree-one prime inputs are field elements.
pub type CircuitInput<F> = crate::runtime::algebra::packing::BaseElement<
    <F as crate::runtime::algebra::PackingField>::Packing,
>;
