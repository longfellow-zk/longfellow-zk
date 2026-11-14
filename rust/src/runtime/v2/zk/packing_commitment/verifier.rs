// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{PackingExtension, PackingField, ZkField},
    v2::{
        dual_packing::generic::PackingProof, polygero::LinearStatement, transcript::TranscriptRef,
    },
};
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub(crate) fn reduce<const W: usize>(
        &self,
        statement: CommitmentStatement<F::E>,
        packing: &PackingProof<F::E>,
        id: &[u8; 32],
        t: &mut TranscriptRef<'_>,
    ) -> Result<LinearStatement<F::E>, String>
    where
        F: ZkField<W>,
    {
        let rows = crate::runtime::v2::dual_packing::verifier::reduce(
            &self.parameters,
            &statement.claim,
            packing,
            id,
            t,
        )?;
        // Dynamic source messages are already bound to this same transcript.
        // Identify the circuit without another query; sparse rows are derived
        // locally rather than accepted as proof data.
        let digest = crate::runtime::v2::proto::Digest { data: *id };
        let (a, b) = self.append_equations::<W>(statement, &rows)?;
        Ok(LinearStatement { a, b, digest })
    }
}
