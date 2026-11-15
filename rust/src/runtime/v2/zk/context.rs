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

//! Deterministic layout derivation for v2.
//!
//! Participant construction takes an interpolation domain with a stable
//! ordered point set, and the participant keeps the domain's field: the
//! prover and verifier use that same domain and field. Circuit metadata
//! determines the witness and pad layout passed to Polygero.
use crate::runtime::algebra::packing::{BaseElement, PackingField};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::{
    core::proto::v2::Circuit,
    runtime::algebra::{range_interpolation::EvaluationDomain, ZkField},
    runtime::v2::{
        polygero::PolygeroParam,
        proto::{polygero::PolygeroConfig, zk::CircuitProofGeometry},
        zk::packing_commitment::{PackingCommitment, PackingLayout},
    },
};

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

/// The Polygero parameter for `cells` frontend cells plus the witness-selection
/// masks the joint commitment appends.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) fn prepare_parameter<F: ZkField, D: EvaluationDomain<F>>(
    cells: usize,
    config: PolygeroConfig,
    domain: &D,
) -> Result<PolygeroParam, String> {
    PolygeroParam::try_new(
        crate::runtime::v2::witness_selection::witness_count(cells)?,
        config,
        domain,
    )
    .map_err(|e| e.to_string())
}

/// Derive the common source layout of `circuits`, the primary circuit
/// first, and one input-aligned sumcheck pad suffix: the proof geometry, the
/// Polygero parameter, the packed commitment and the validated shared input
/// layout. The caller still validates the parameter as a selected field.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) fn prepare_circuit_layout<
    F: ZkField + PackingField,
    D: EvaluationDomain<F>,
    X: crate::runtime::algebra::packing::PackingExtension<Ambient = F>,
>(
    circuits: &[&Circuit<F>],
    virtual_inputs: usize,
    config: PolygeroConfig,
    extension: X,
    domain: &D,
) -> Result<
    (
        CircuitProofGeometry,
        PolygeroParam,
        PackingCommitment<X>,
        InputLayout,
    ),
    String,
> {
    if domain.field().is_binary() && !extension.binary128_profile() {
        return Err("binary circuits require the authenticated bit-input packing profile".into());
    }
    let inputs = InputLayout::new(circuits, virtual_inputs)?;
    let sc_geom = crate::runtime::v2::sumcheck::circuit_geometry(circuits)?;
    let layout = PackingLayout::new(inputs.committed(), sc_geom.pad_count(), extension.degree())?;
    let param = prepare_parameter(layout.witness_count, config, domain)?;
    let geometry = CircuitProofGeometry::new(sc_geom, layout.degree, param.geometry().nw)
        .map_err(|e| e.to_string())?;
    let backend = PackingCommitment::new(domain.field().clone(), layout, extension)?;
    Ok((geometry, param, backend, inputs))
}

/// The shared input array of a participant's components:
/// `[public | committed private | virtual]`.
///
/// Its width is the largest component width. Virtual entries are neither public
/// nor committed: each proof defines them as affine functions of committed
/// inputs, and constraint compilation substitutes those definitions. The
/// primary circuit must end before the virtual suffix, so it cannot read it.
///
/// Layouts come only from validated construction. The type is private to the
/// crate, so no caller outside it can write an inconsistent one as a literal:
///
/// ```compile_fail,E0603
/// use longfellow_zk::runtime::v2::zk::InputLayout;
/// let _ = InputLayout { npublic: 2, committed_end: 1, ninput: 0 };
/// ```
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct InputLayout {
    // Invariant, established by `new`: npublic <= committed_end <= ninput.
    /// Inputs before the committed private range.
    pub(crate) npublic: usize,
    /// End of the committed private range; the virtual suffix starts here.
    pub(super) committed_end: usize,
    /// Width of the shared input array.
    pub(crate) ninput: usize,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl InputLayout {
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
    pub(super) fn committed(&self) -> usize {
        self.committed_end - self.npublic
    }
    pub(crate) fn virtual_count(&self) -> usize {
        self.ninput - self.committed_end
    }
}

/// One virtual input entry: `constant + coefficient * input[source]`, where
/// `source` is an absolute index into the committed private inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) struct VirtualInput<E> {
    pub(crate) source: usize,
    pub(crate) constant: E,
    pub(crate) coefficient: E,
}

/// Per-proof definitions of a participant's virtual input suffix, in order.
/// Both roles derive them from the transcript; they are never absorbed.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) struct VirtualInputs<E> {
    pub(crate) entries: Vec<VirtualInput<E>>,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl<E> VirtualInputs<E> {
    pub(crate) fn none() -> Self {
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
pub type CircuitInput<F> = BaseElement<<F as PackingField>::Packing>;
