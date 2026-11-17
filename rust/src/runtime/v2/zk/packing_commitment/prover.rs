// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{
        packing::{AmbientElement, BaseElement, PackingExtension},
        ZkField,
    },
    random::PrivateRandom,
    v2::{
        dual_packing::prover::{prove_packed, PackingMasks},
        polygero::LinearStatement,
        proto::dual_packing::PackingProof,
        transcript::Bound,
    },
};
pub(crate) struct PreparedInputs<E> {
    packed: Vec<E>,
}
pub(crate) struct PackingState<E> {
    words: Vec<E>,
    suffix: Vec<E>,
    masks: PackingMasks<E>,
}
impl<X: PackingExtension> PackingCommitment<X> {
    pub(crate) fn prepare_inputs(
        &self,
        logical: &[BaseElement<X>],
    ) -> Result<PreparedInputs<AmbientElement<X>>, String> {
        if logical.len() != self.layout.private_inputs {
            return Err("witness length mismatch".into());
        }
        Ok(PreparedInputs {
            packed: self.parameters.pack(logical)?,
        })
    }
    pub(crate) fn prepare(
        &self,
        inputs: PreparedInputs<AmbientElement<X>>,
        suffix: Vec<AmbientElement<X>>,
        rng: &mut impl PrivateRandom,
    ) -> (PackingState<AmbientElement<X>>, Vec<AmbientElement<X>>) {
        let f = self.parameters.field();
        let masks = PackingMasks::sample(&self.parameters, || rng.elt_field(f));
        // Only nontrivial packing needs the words again after commitment.
        let words = if self.layout.degree > 1 {
            inputs.packed.clone()
        } else {
            Vec::new()
        };
        // Frontend values in value order (packed words, then pads), then the
        // packing masks.
        let mut witness = inputs.packed;
        witness.extend_from_slice(&suffix);
        witness.extend_from_slice(masks.cells());
        (
            PackingState {
                words,
                suffix,
                masks,
            },
            witness,
        )
    }
    /// Reduce the input claim on the packing parameters bound to `t`.
    pub(crate) fn prove(
        t: &mut Bound<'_, Self>,
        state: PackingState<AmbientElement<X>>,
        statement: CommitmentStatement<AmbientElement<X>>,
    ) -> Result<
        (
            PackingProof<AmbientElement<X>>,
            LinearStatement<AmbientElement<X>>,
        ),
        String,
    >
    where
        X::Ambient: ZkField,
    {
        let (packing, rows) = prove_packed(
            &mut t.project(|c| &c.parameters),
            &statement.claim,
            &state.words,
            &state.suffix,
            state.masks,
        )?;
        drop(state.words);
        drop(state.suffix);
        // The transcript already holds the statement and the sumcheck and
        // packing messages these rows derive from.
        let (a, b) = t.part().append_equations(statement, &rows)?;
        Ok((
            packing,
            LinearStatement {
                a,
                b,
                session: t.session(),
            },
        ))
    }
}
