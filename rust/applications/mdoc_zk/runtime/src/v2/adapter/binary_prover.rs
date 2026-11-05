// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::{
    algebra::PackingExtension,
    polygero::LinearStatement,
    proto::zk_v2::CircuitProof,
    random::RandomEngine,
    sumcheck_v2::{SumcheckProof, TranscriptSumcheck},
    zk_v2::{commitment::PackingState, constraint_compiler::compile_packed},
};
pub(in crate::mdoc::runtime::v2) struct BinaryState {
    id: [u8; 32],
    config: crate::runtime::polygero::PolygeroConfig,
    pads: SumcheckProof<2, F>,
    packing: PackingState<E>,
}
impl BinaryParticipant {
    pub fn prepare(
        &self,
        private: &[bool],
        rng: &mut impl RandomEngine,
    ) -> Result<(BinaryState, Vec<E>), String> {
        let input = self.backend.prepare_inputs(private)?;
        let (pads, suffix) =
            sumcheck_v2::sample_pads(&self.geometry.sc_geom, rng, self.backend.parameters.field());
        let (packing, witness) = self.backend.prepare(input, suffix, rng);
        Ok((
            BinaryState {
                id: self.id,
                config: self.config,
                pads,
                packing,
            },
            witness,
        ))
    }
    pub fn prove<D: EvaluationDomain<2, F>>(
        &self,
        c: &Circuit<F>,
        public: &[bool],
        private: Vec<bool>,
        state: BinaryState,
        values: &[E],
        t: &mut Transcript,
        ctx: &ZkContext<'_, 2, F, D>,
    ) -> Result<(CircuitProof<2, F>, LinearStatement<E>), String> {
        let tree = self.circuit(c, public, values)?;
        if state.id != self.id
            || state.config != self.config
            || private.len() != self.backend.layout.private_inputs
        {
            return Err("binary state or witness shape".into());
        }
        state
            .pads
            .validate(&self.geometry.sc_geom)
            .map_err(|e| e.to_string())?;
        let extension = self.backend.parameters.extension();
        let public = extension.input_elements(ctx.f, public);
        let mut inputs = public.to_vec();
        inputs.extend(extension.into_input_elements(ctx.f, private));
        for c in [c, &tree] {
            t.write_sumcheck_statement(c, &public, ctx.f);
        }
        let (sumcheck_proof, constraints) =
            sumcheck_v2::evaluate_and_prove_circuits(&[c, &tree], inputs, &state.pads, t, ctx.f)?;
        let pads = self
            .geometry
            .sc_geom
            .pad_layout(self.backend.layout.suffix_start);
        let statement = compile_packed(constraints, &pads, &public, &self.backend.layout, ctx.f)?;
        let (packing, statement) =
            self.backend
                .prove::<2>(state.packing, statement, &self.id, t)?;
        Ok((
            CircuitProof {
                sumcheck_proof,
                packing,
            },
            statement,
        ))
    }
}
