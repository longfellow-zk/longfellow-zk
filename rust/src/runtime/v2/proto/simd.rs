// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Internal typed messages shared by packed prover and verifier reductions.
use super::sumcheck::LayerProof;
use crate::core::algebra::{ElementOf, SerializableField};
#[derive(Clone, Debug)]
pub(crate) struct SimdAdapterProof<E> {
    pub u: [E; 128],
    pub a: E,
}
#[derive(Clone, Debug)]
pub(crate) struct SimdProof<F: SerializableField> {
    pub nonlinear: ElementOf<F>,
    pub dot: LayerProof<F>,
    pub adapter: SimdAdapterProof<ElementOf<F>>,
}

use super::polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment};
use crate::runtime::algebra::gf2_128::{Gf2_128, Gf2_128Field};
pub(crate) const MAGIC: &[u8; 8] = b"SIMDPCS4";
pub(crate) struct SimdEnvelope {
    pub root: PolygeroCommitment,
    pub reduction: SimdProof<Gf2_128Field>,
    pub opening: JointPolygeroProof<(FieldProof<Gf2_128>, ())>,
}
