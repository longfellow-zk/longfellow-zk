// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{PackingExtension, PackingField, ZkField},
    dual_packing::generic::PackingProof,
    polygero::LinearStatement,
    random::Transcript,
};
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub fn verify<const W: usize>(
        &self,
        statement: CommitmentStatement<F::E>,
        packing: &PackingProof<F::E>,
        id: &[u8; 32],
        t: &mut Transcript,
    ) -> Result<LinearStatement<F::E>, String>
    where
        F: ZkField<W>,
    {
        let rows = crate::runtime::dual_packing::verifier::verify(
            &self.parameters,
            &statement.claim,
            packing,
            id,
            t,
        )?;
        // Bind the same source prefix as the prover, before backend batching.
        // The sparse rows below are derived locally rather than accepted as proof data.
        let digest = super::super::transcript::statement_digest(t);
        let (a, b) = self.authenticate::<W>(statement, &rows)?;
        Ok(LinearStatement { a, b, digest })
    }
}
