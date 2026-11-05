// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{PackingExtension, PackingField, ZkField},
    dual_packing::generic::{PackingMasks, PackingProof},
    polygero::LinearStatement,
    random::{RandomEngine, Transcript},
};
pub(in crate::runtime::zk_v2) struct PreparedInputs<E> {
    packed: Vec<E>,
}
pub(in crate::runtime::zk_v2) struct PackingState<E> {
    words: Vec<E>,
    suffix: Vec<E>,
    masks: PackingMasks<E>,
}
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub fn prepare_inputs(
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
    pub fn prepare(
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
        let mut witness = inputs.packed;
        witness.extend_from_slice(masks.cells());
        witness.extend_from_slice(&suffix);
        (
            PackingState {
                words,
                suffix,
                masks,
            },
            witness,
        )
    }
    pub fn prove<const W: usize>(
        &self,
        state: PackingState<F::E>,
        statement: CommitmentStatement<F::E>,
        id: &[u8; 32],
        t: &mut Transcript,
    ) -> Result<(PackingProof<F::E>, LinearStatement<F::E>), String>
    where
        F: ZkField<W>,
    {
        let (packing, rows) = crate::runtime::dual_packing::prover::prove_packed(
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
        // This prefix binds the circuit, public inputs, sumcheck and packing
        // messages from which both roles reconstruct the affine statement.
        let digest = super::super::transcript::statement_digest(t);
        let (a, b) = self.authenticate::<W>(statement, &rows)?;
        Ok((packing, LinearStatement { a, b, digest }))
    }
}
