// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{PackingExtension, PackingField, ZkField},
    random::RandomEngine,
    v2::{
        dual_packing::generic::{PackingMasks, PackingProof},
        polygero::LinearStatement,
        transcript::TranscriptRef,
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
        logical: &[crate::runtime::algebra::packing::BaseElement<X>],
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
        rng: &mut impl RandomEngine,
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
    pub(crate) fn prove<const W: usize>(
        &self,
        state: PackingState<F::E>,
        statement: CommitmentStatement<F::E>,
        id: &[u8; 32],
        t: &mut TranscriptRef<'_>,
    ) -> Result<(PackingProof<F::E>, LinearStatement<F::E>), String>
    where
        F: ZkField<W>,
    {
        let (packing, rows) = crate::runtime::v2::dual_packing::prover::prove_packed(
            &self.parameters,
            &statement.claim,
            &state.words,
            &state.suffix,
            state.masks,
            id,
            t,
        )?;
        drop(state.words);
        drop(state.suffix);
        // The continuing transcript already binds the public inputs, sumcheck
        // and packing messages. The circuit ID identifies their source without
        // introducing a query between the frontend and joint batching.
        let digest = crate::runtime::v2::proto::Digest { data: *id };
        let (a, b) = self.append_equations::<W>(statement, &rows)?;
        Ok((packing, LinearStatement { a, b, digest }))
    }
}
