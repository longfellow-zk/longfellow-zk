// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    polygero::LinearStatement,
    proto::{sumcheck::PackedReduction, zk::CircuitProof},
    simd_sumcheck::{shared, NativeRow},
    sumcheck,
    zk::{constraint_compiler::compile_packed, VirtualInputs},
};
impl BinaryParticipant {
    /// Reduce the relation and the fragment to this field's statement.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::mldsa::runtime) fn reduce(
        t: &mut Bound<'_, Self>,
        c: &Circuit<F>,
        fragment: &Circuit<F>,
        public: &[E],
        proof: &CircuitProof<F>,
        simd: Option<&PackedReduction<F>>,
        leaves: &VirtualInputs<E>,
    ) -> Result<LinearStatement<E>, String> {
        let p = t.part();
        p.check(c, fragment, public)?;
        leaves.validate(&p.inputs)?;
        proof
            .sumcheck_proof
            .validate(p.geometry.sumcheck())
            .map_err(|e| e.to_string())?;
        let f = p.backend.parameters.field();
        let constraints = sumcheck::derive_constraints_for_circuits(
            &[c, fragment],
            &proof.sumcheck_proof,
            &mut t.transcript(),
            f,
        )?;
        if let Some(s) = &p.simd {
            let layout = p.simd_layout(s)?;
            let pads = p.geometry.sumcheck().pad_layout(layout.suffix_start);
            let statement = compile_packed::<F>(constraints, &pads, public, &layout, leaves, f)?;
            let (weights, constant, terms, a, b) = statement.into_parts(layout.suffix_start);
            let claim = shared::ScalarClaim {
                weights,
                rhs: NativeRow { constant, terms },
            };
            let rows = s.program().reduce_shared(
                simd.ok_or("missing SIMD reduction")?,
                &proof.packing,
                claim,
                s.placements(),
                layout.witness_count,
                &mut t.transcript(),
            )?;
            Ok(p.statement(a, b, rows, t.session()))
        } else {
            if simd.is_some() {
                return Err("unexpected SIMD reduction".into());
            }
            let pads = p
                .geometry
                .sumcheck()
                .pad_layout(p.backend.layout.suffix_start);
            let statement =
                compile_packed::<F>(constraints, &pads, public, &p.backend.layout, leaves, f)?;
            PackingCommitment::reduce(&mut t.project(|b| &b.backend), statement, &proof.packing)
        }
    }
}
