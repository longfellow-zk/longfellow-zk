// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{
        packing::{BaseElement, PackingExtension, PackingField},
        ZkField,
    },
    random::PrivateRandom,
    v2::{
        dual_packing::{
            generic::{PackingMasks, PackingProof},
            prover::prove_packed,
        },
        polygero::LinearStatement,
        proto::Digest,
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
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub(crate) fn prepare_inputs(
        &self,
        logical: &[BaseElement<X>],
    ) -> Result<PreparedInputs<F::E>, String> {
        if logical.len() != self.layout.private_inputs {
            return Err("witness length mismatch".into());
        }
        Ok(PreparedInputs {
            packed: self.parameters.pack(logical)?,
        })
    }
    pub(crate) fn prepare(
        &self,
        inputs: PreparedInputs<F::E>,
        suffix: Vec<F::E>,
        rng: &mut impl PrivateRandom,
    ) -> (PackingState<F::E>, Vec<F::E>) {
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
    pub(crate) fn prove<const W: usize>(
        t: &mut Bound<'_, Self>,
        state: PackingState<F::E>,
        statement: CommitmentStatement<F::E>,
        id: &[u8; 32],
    ) -> Result<(PackingProof<F::E>, LinearStatement<F::E>), String>
    where
        F: ZkField<W>,
    {
        let (packing, rows) = prove_packed(
            &mut t.project(|c| &c.parameters),
            &statement.claim,
            &state.words,
            &state.suffix,
            state.masks,
            id,
        )?;
        drop(state.words);
        drop(state.suffix);
        // The continuing transcript already binds the public inputs, sumcheck
        // and packing messages. The circuit ID identifies their source without
        // introducing a query between the frontend and joint batching.
        let digest = Digest { data: *id };
        let (a, b) = t.part().append_equations::<W>(statement, &rows)?;
        Ok((packing, LinearStatement { a, b, digest }))
    }
}
