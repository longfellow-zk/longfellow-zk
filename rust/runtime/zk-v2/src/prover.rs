// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! One v2 prover over the field-selected packing commitment.
use crate::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{
            packing::{IdentityExtension, PackingExtension, PackingField},
            EvaluationDomain, ZkField,
        },
        polygero::PolygeroConfig,
        random::{RandomEngine, Transcript},
        sumcheck_v2::{self, SumcheckProof, TranscriptSumcheck},
        zk_v2::{
            commitment::CommitmentState,
            context::{prepare_layout, private_input_count},
            ZkContext, ZkProof, ZkProofGeometry,
        },
    },
};
pub struct ZkProver<
    const W: usize,
    F: ZkField<W>,
    X: PackingExtension<Ambient = F> = <F as PackingField>::Packing,
> {
    pub(super) circuit: Circuit<F>,
    config: PolygeroConfig,
    extension: fn(&F) -> X,
    kernel: Option<
        fn(
            Vec<F::E>,
            &SumcheckProof<W, F>,
            &Circuit<F>,
            &mut Transcript,
            &F,
            usize,
        ) -> Result<
            (
                SumcheckProof<W, F>,
                sumcheck_v2::symbolic::Constraints<F::E>,
            ),
            String,
        >,
    >,
    window: usize,
}
pub struct ZkProverCommitment<
    const W: usize,
    F: ZkField<W>,
    X: PackingExtension<Ambient = F> = <F as PackingField>::Packing,
> {
    pads: SumcheckProof<W, F>,
    inner: CommitmentState<W, F, X>,
    circuit_id: [u8; 32],
    config: PolygeroConfig,
}
impl<const W: usize, F: ZkField<W>> ZkProver<W, F> {
    pub fn new(circuit: Circuit<F>, config: PolygeroConfig) -> Self {
        Self {
            circuit,
            config,
            extension: F::packing_extension,
            kernel: None,
            window: 0,
        }
    }
    pub fn new_full_field(
        circuit: Circuit<F>,
        config: PolygeroConfig,
    ) -> ZkProver<W, F, IdentityExtension<F>> {
        ZkProver {
            circuit,
            config,
            extension: |f| IdentityExtension::new(f.clone()),
            kernel: None,
            window: 0,
        }
    }
}
impl<const W: usize, F: ZkField<W>, X: PackingExtension<Ambient = F>> ZkProver<W, F, X> {
    pub fn with_extension(
        circuit: Circuit<F>,
        config: PolygeroConfig,
        extension: fn(&F) -> X,
    ) -> Self {
        Self {
            circuit,
            config,
            extension,
            kernel: None,
            window: 0,
        }
    }
    pub fn commit<D: EvaluationDomain<W, F>, R: RandomEngine>(
        &self,
        private: Vec<F::E>,
        ctx: &ZkContext<'_, W, F, D>,
        t: &mut Transcript,
        rng: &mut R,
    ) -> Result<(ZkProverCommitment<W, F, X>, ZkProofGeometry), String> {
        if private.len() != private_input_count(&self.circuit) {
            return Err("witness length mismatch".into());
        }
        let (geometry, param, backend) =
            prepare_layout(&self.circuit, self.config, (self.extension)(ctx.f), ctx)?;
        let prepared = backend.prepare_inputs(private)?;
        let (pads, suffix) = sumcheck_v2::sample_pads(&geometry.sc_geom, rng, ctx.f);
        let inner = backend.commit(
            prepared,
            suffix,
            param,
            &self.circuit.id,
            t,
            rng,
            ctx.domain,
        )?;
        Ok((
            ZkProverCommitment {
                pads,
                inner,
                circuit_id: self.circuit.id,
                config: self.config,
            },
            geometry,
        ))
    }
    pub fn prove<D: EvaluationDomain<W, F>>(
        &self,
        public: &[F::E],
        mut state: ZkProverCommitment<W, F, X>,
        t: &mut Transcript,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<ZkProof<W, F>, String> {
        if public.len() != self.circuit.raw.npublic_input {
            return Err("public inputs length mismatch".into());
        }
        if state.circuit_id != self.circuit.id || state.config != self.config {
            return Err("commitment belongs to another circuit or configuration".into());
        }
        let geometry = sumcheck_v2::SumcheckProofGeometry::from_circuit(&self.circuit);
        state.pads.validate(&geometry).map_err(|e| e.to_string())?;
        t.write_sumcheck_statement(&self.circuit, public, ctx.f);
        let mut inputs = Vec::with_capacity(public.len() + state.inner.private.len());
        inputs.extend_from_slice(public);
        inputs.extend(std::mem::take(&mut state.inner.private));
        let (sumcheck_proof, constraints) = if let Some(kernel) = self
            .kernel
            .filter(|_| public.iter().all(|x| ctx.f.is_zero(x) || *x == ctx.f.one()))
        {
            kernel(inputs, &state.pads, &self.circuit, t, ctx.f, self.window)?
        } else {
            let layers = sumcheck_v2::eval_circuit(inputs, &self.circuit, ctx.f)
                .map_err(|e| format!("eval_circuit failed: {e}"))?;
            sumcheck_v2::prove_core(layers, &state.pads, &self.circuit, t, ctx.f)
        };
        let pads = geometry.pad_layout(state.inner.backend.layout.suffix_start);
        let statement = super::constraint_compiler::compile::<W, F>(
            constraints,
            &pads,
            public,
            &state.inner.backend.layout,
            ctx.f,
        )?;
        let com = state.inner.commitment.clone();
        let (packing, com_proof) = state
            .inner
            .prove(statement, &self.circuit.id, t, ctx.domain)?;
        Ok(ZkProof {
            sumcheck_proof,
            com,
            packing,
            com_proof,
        })
    }
}
#[cfg(test)]
#[path = "../tests/prover.rs"]
mod tests;

#[cfg(feature = "experimental")]
impl ZkProver<2, crate::runtime::algebra::gf2_128::Gf2_128Field> {
    pub fn with_boolean_window(mut self, window: usize) -> Result<Self, String> {
        if !(1..=4).contains(&window) {
            return Err("Boolean window must be 1 through 4".into());
        }
        self.window = window;
        self.kernel = Some(sumcheck_v2::boolean::prove_core);
        Ok(self)
    }
}
