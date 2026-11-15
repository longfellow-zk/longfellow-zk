// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The hidden-key binary host: the signature relation and the adapter's fixed
//! fragment in one layered sumcheck over one committed source.
//!
//! It is `zk::joint::CircuitParticipant` with two differences. Its public
//! inputs are full GF(2^128) challenges (the permutation points gamma), and
//! with SIMD SHAKE it packs its source with the shared SIMD program instead of
//! input packing. Both share the fragment's virtual leaves and the constraint
//! compiler that substitutes them.
use std::sync::Arc;

use super::KeccakSource;
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{
            gf2_128::{Gf2_128 as E, Gf2_128Field as F},
            packing::PackingField,
            range_interpolation::EvaluationDomain,
        },
        v2::{
            polygero,
            polygero::PolygeroParam,
            proto::{polygero::PolygeroConfig, zk::CircuitProofGeometry},
            simd_sumcheck,
            transcript::{Bound, SessionStamp},
            witness_selection::Field,
            zk::{
                context::{prepare_circuit_layout, prepare_parameter},
                packing_commitment::{PackingCommitment, PackingLayout},
                InputLayout,
            },
        },
    },
};
pub(in crate::mldsa::runtime) struct BinaryParticipant {
    simd: Option<Arc<KeccakSource>>,
    geometry: CircuitProofGeometry,
    backend: PackingCommitment<<F as PackingField>::Packing>,
    param: PolygeroParam,
    id: [u8; 32],
    fragment_id: [u8; 32],
    config: PolygeroConfig,
    inputs: InputLayout,
}
impl BinaryParticipant {
    /// `c` and the adapter's `fragment` share one input array whose last
    /// `virtual_inputs` entries are the fragment's leaves.
    pub(in crate::mldsa::runtime) fn new<D: EvaluationDomain<F>>(
        c: &Circuit<F>,
        fragment: &Circuit<F>,
        virtual_inputs: usize,
        config: PolygeroConfig,
        domain: &D,
    ) -> Result<Self, String> {
        let (geometry, param, backend, inputs) = prepare_circuit_layout(
            &[c, fragment],
            virtual_inputs,
            config,
            domain.field().packing_extension(),
            domain,
        )?;
        Ok(Self {
            simd: None,
            geometry,
            backend,
            param,
            config,
            id: c.id,
            fragment_id: fragment.id,
            inputs,
        })
    }
    pub(in crate::mldsa::runtime) fn with_simd<D: EvaluationDomain<F>>(
        mut self,
        source: Arc<KeccakSource>,
        domain: &D,
    ) -> Result<Self, String> {
        if source.placements().len() != self.backend.layout.private_inputs {
            return Err("SIMD private layout".into());
        }
        self.param = prepare_parameter(
            source.program().cell_count() + self.geometry.sumcheck().pad_count(),
            self.config,
            domain,
        )?;
        self.geometry = CircuitProofGeometry::new(
            self.geometry.sumcheck().clone(),
            128,
            self.param.geometry().nw,
        )
        .map_err(|e| e.to_string())?;
        self.simd = Some(source);
        Ok(self)
    }
    pub(in crate::mldsa::runtime) fn geometry(&self) -> CircuitProofGeometry {
        self.geometry.clone()
    }
    pub(in crate::mldsa::runtime) fn participant<'a, D: EvaluationDomain<F>>(
        &self,
        domain: &'a D,
    ) -> Result<Field<'a, F, D>, String> {
        Field::new(self.param.clone(), domain)
    }
    /// The layout of the SIMD source: the program's cells, then the pads.
    fn simd_layout(&self, s: &KeccakSource) -> Result<PackingLayout, String> {
        let base = s.program().cell_count();
        let pad_cells = self.geometry.sumcheck().pad_count();
        PackingLayout::for_simd_source(self.backend.layout.private_inputs, base, pad_cells)
    }
    fn statement(
        &self,
        mut a: Vec<polygero::PolygeroLinearTerm<E>>,
        mut b: Vec<E>,
        rows: Vec<simd_sumcheck::NativeRow>,
        session: SessionStamp,
    ) -> polygero::LinearStatement<E> {
        for row in rows {
            let c = b.len();
            b.push(row.constant);
            a.extend(
                row.terms
                    .into_iter()
                    .map(|(w, k)| polygero::PolygeroLinearTerm { c, w, k }),
            );
        }
        polygero::LinearStatement { a, b, session }
    }
    /// Check that the circuits and public inputs are this participant's.
    fn check(&self, c: &Circuit<F>, fragment: &Circuit<F>, public: &[E]) -> Result<(), String> {
        if c.id != self.id
            || fragment.id != self.fragment_id
            || public.len() != self.inputs.npublic
            || InputLayout::new(&[c, fragment], self.inputs.virtual_count())? != self.inputs
        {
            return Err("binary circuit statement mismatch".into());
        }
        Ok(())
    }
}
cfg_prover! {mod prover;}
cfg_verifier! {mod verifier;}

mod transcript;
