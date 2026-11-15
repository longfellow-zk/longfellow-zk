// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::packing::PackingExtension,
        random::PrivateRandom,
        v2::{
            polygero::LinearStatement,
            proto::{sumcheck::PackedReduction, zk::CircuitProof},
            simd_sumcheck::{shared, NativeRow, SharedState},
            sumcheck,
            sumcheck::SumcheckPads,
            zk::{
                constraint_compiler::compile_packed,
                packing_commitment::prover::PackingState as ScalarPacking, VirtualInputs,
            },
        },
    },
};
pub(in crate::mldsa::runtime) struct BinaryState<'p> {
    participant: &'p BinaryParticipant,
    pads: SumcheckPads<F>,
    packing: Packing,
}
// Keep the prepared SIMD state inline to avoid another allocation per proof.
#[allow(clippy::large_enum_variant)]
enum Packing {
    Scalar(ScalarPacking<E>),
    Simd(SharedState),
}
impl BinaryParticipant {
    pub(in crate::mldsa::runtime) fn prepare(
        &self,
        private: &[bool],
        rng: &mut impl PrivateRandom,
    ) -> Result<(BinaryState<'_>, Vec<E>), String> {
        let (pads, suffix) = sumcheck::sample_pads(
            self.geometry.sumcheck(),
            rng,
            self.backend.parameters.field(),
        );
        let (packing, witness) = if let Some(s) = &self.simd {
            let input = s.witness(private)?;
            let (state, w) = s.program().prepare_shared(input, suffix, rng)?;
            (Packing::Simd(state), w)
        } else {
            let input = self.backend.prepare_inputs(private)?;
            let (state, w) = self.backend.prepare(input, suffix, rng);
            (Packing::Scalar(state), w)
        };
        Ok((
            BinaryState {
                participant: self,
                pads,
                packing,
            },
            witness,
        ))
    }
    /// Prove the relation and the fragment. `leaves` defines the virtual
    /// inputs; it must be fixed before this call draws any challenge.
    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    pub(in crate::mldsa::runtime) fn prove(
        t: &mut Bound<'_, Self>,
        c: &Circuit<F>,
        fragment: &Circuit<F>,
        public: &[E],
        private: Vec<bool>,
        prepared: BinaryState<'_>,
        leaves: &VirtualInputs<E>,
    ) -> Result<
        (
            CircuitProof<F>,
            Option<PackedReduction<F>>,
            LinearStatement<E>,
        ),
        String,
    > {
        let p = t.part();
        p.check(c, fragment, public)?;
        leaves.validate(&p.inputs)?;
        let original = prepared.participant;
        let same_source = match (&original.simd, &p.simd) {
            (None, None) => true,
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            _ => false,
        };
        if original.id != p.id
            || original.fragment_id != p.fragment_id
            || original.config != p.config
            || original.geometry != p.geometry
            || original.inputs != p.inputs
            || original.backend.layout != p.backend.layout
            || !same_source
            || private.len() != p.backend.layout.private_inputs
        {
            return Err("binary state or witness shape".into());
        }
        prepared
            .pads
            .validate(p.geometry.sumcheck())
            .map_err(|e| e.to_string())?;
        let f = p.backend.parameters.field();
        let extension = p.backend.parameters.extension();
        let mut inputs = Vec::with_capacity(p.inputs.ninput);
        inputs.extend_from_slice(public);
        inputs.extend(extension.into_input_elements(f, private));
        for v in &leaves.entries {
            let value = f.addf(&v.constant, &f.mulf(&v.coefficient, &inputs[v.source]));
            inputs.push(value);
        }
        let (sumcheck_proof, constraints) = sumcheck::evaluate_and_prove_circuits(
            &[c, fragment],
            inputs,
            prepared.pads,
            &mut t.transcript(),
            f,
        )?;
        let (packing, simd, statement) = match prepared.packing {
            Packing::Scalar(scalar_state) => {
                if p.simd.is_some() {
                    return Err("binary packing state kind".into());
                }
                let pads = p
                    .geometry
                    .sumcheck()
                    .pad_layout(p.backend.layout.suffix_start);
                let statement =
                    compile_packed(constraints, &pads, public, &p.backend.layout, leaves, f)?;
                let (packing, scalar_statement) = PackingCommitment::prove(
                    &mut t.project(|b| &b.backend),
                    scalar_state,
                    statement,
                )?;
                (packing, None, scalar_statement)
            }
            Packing::Simd(simd_state) => {
                let s = p.simd.as_ref().ok_or("binary packing state kind")?;
                let layout = p.simd_layout(s)?;
                let pads = p.geometry.sumcheck().pad_layout(layout.suffix_start);
                let statement = compile_packed(constraints, &pads, public, &layout, leaves, f)?;
                let (weights, constant, terms, a, b) = statement.into_parts(layout.suffix_start);
                let claim = shared::ScalarClaim {
                    weights,
                    rhs: NativeRow { constant, terms },
                };
                let (proof, packing, rows) = s.program().prove_shared(
                    simd_state,
                    claim,
                    s.placements(),
                    &mut t.transcript(),
                )?;
                (packing, Some(proof), p.statement(a, b, rows, t.session()))
            }
        };
        Ok((
            CircuitProof {
                sumcheck_proof,
                packing,
            },
            simd,
            statement,
        ))
    }
}
