// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{
    algebra::PackingExtension,
    v2::{
        polygero::LinearStatement, proto::zk::CircuitProof, sumcheck::TranscriptSumcheck,
        zk::constraint_compiler::compile_packed,
    },
};
impl BinaryParticipant {
    pub fn verify<D: EvaluationDomain<2, F>>(
        &self,
        c: &Circuit<F>,
        public: &[bool],
        proof: &CircuitProof<2, F>,
        values: &[E],
        t: &mut Transcript,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<LinearStatement<E>, String> {
        let tree = self.circuit(c, public, values)?;
        proof
            .sumcheck_proof
            .validate(&self.geometry.sc_geom)
            .map_err(|e| e.to_string())?;
        let public = self
            .backend
            .parameters
            .extension()
            .input_elements(ctx.f, public);
        for c in [c, &tree] {
            t.write_sumcheck_statement(c, &public, ctx.f);
        }
        let constraints = sumcheck::derive_constraints_for_circuits(
            &[c, &tree],
            &proof.sumcheck_proof,
            t,
            ctx.f,
        )?;
        let pads = self
            .geometry
            .sc_geom
            .pad_layout(self.backend.layout.suffix_start);
        let statement =
            compile_packed::<2, F>(constraints, &pads, &public, &self.backend.layout, ctx.f)?;
        self.backend
            .verify::<2>(statement, &proof.packing, &self.id, t)
    }
}
