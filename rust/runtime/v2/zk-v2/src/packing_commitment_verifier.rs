// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{PackingExtension, PackingField, ZkField},
    dual_packing::generic::PackingProof,
    polygero::LinearStatement,
    random::transcript_v2::Transcript,
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
        // Dynamic source messages are already bound to this same transcript.
        // Identify the circuit without another query; sparse rows are derived
        // locally rather than accepted as proof data.
        let digest = crate::runtime::proto::Digest { data: *id };
        let (a, b) = self.authenticate::<W>(statement, &rows)?;
        Ok(LinearStatement { a, b, digest })
    }
}
