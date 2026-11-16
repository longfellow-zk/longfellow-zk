// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{
        packing::{PackingExtension, PackingField},
        ZkField,
    },
    v2::{polygero::LinearStatement, proto::dual_packing::PackingProof, transcript::Bound},
};
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    /// Replay the packing reduction on the parameters bound to `t`.
    pub(crate) fn reduce(
        t: &mut Bound<'_, Self>,
        statement: CommitmentStatement<F::E>,
        packing: &PackingProof<F::E>,
    ) -> Result<LinearStatement<F::E>, String>
    where
        F: ZkField,
    {
        let rows = crate::runtime::v2::dual_packing::verifier::reduce(
            &mut t.project(|c| &c.parameters),
            &statement.claim,
            packing,
        )?;
        // The source messages are already absorbed; sparse rows are derived
        // locally rather than accepted as proof data.
        let (a, b) = t.part().append_equations(statement, &rows)?;
        Ok(LinearStatement {
            a,
            b,
            session: t.session(),
        })
    }
}
