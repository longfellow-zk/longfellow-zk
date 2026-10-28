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
use crate::runtime::algebra::ZkField;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::{
    core::proto::circuit::Circuit,
    runtime::{
        algebra::EvaluationDomain,
        polygero::{PolygeroConfig, PolygeroParam},
        proto::zk_v2::packing_layout_with_degree,
        zk_v2::commitment::PackingCommitment,
        zk_v2::ZkProofGeometry,
    },
};

/// Borrow the field implementation and ordered interpolation domain for an invocation.
pub struct ZkContext<'a, const W: usize, F: ZkField<W>, D> {
    pub f: &'a F,
    pub domain: &'a D,
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

/// Derive the complete public layout from a trusted circuit and fixed config.
/// Both roles use the same witness count, pad products, and proof dimensions.
/// Product coordinates are local to construction; Polygero retains its own copy.
/// This prepares metadata only, with no polynomial samples or interpolation plans.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) fn prepare_layout<
    const W: usize,
    F: ZkField<W>,
    D: EvaluationDomain<W, F>,
    X: crate::runtime::algebra::PackingExtension<Ambient = F>,
>(
    circuit: &Circuit<F>,
    config: PolygeroConfig,
    extension: X,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<(ZkProofGeometry, PolygeroParam, PackingCommitment<F, X>), String> {
    let (layout, sc_geom, products) = packing_layout_with_degree(circuit, extension.degree())?;
    let param = PolygeroParam::try_new(layout.witness_count, &products, config, ctx.domain, ctx.f)
        .map_err(|e| e.to_string())?;
    let geometry = ZkProofGeometry {
        sc_geom,
        com_geom: param.geometry(),
        packing_degree: layout.degree,
    };
    let backend = PackingCommitment::new(ctx.f.clone(), layout, extension)?;
    Ok((geometry, param, backend))
}
