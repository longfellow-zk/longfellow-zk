// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{
        packing::{AmbientElement, PackingExtension},
        ZkField,
    },
    v2::{polygero::LinearStatement, proto::dual_packing::PackingProof, transcript::Bound},
};
impl<X: PackingExtension> PackingCommitment<X> {
    /// Replay the packing reduction on the parameters bound to `t`.
    pub(crate) fn reduce(
        t: &mut Bound<'_, Self>,
        statement: CommitmentStatement<AmbientElement<X>>,
        packing: &PackingProof<AmbientElement<X>>,
    ) -> Result<LinearStatement<AmbientElement<X>>, String>
    where
        X::Ambient: ZkField,
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
