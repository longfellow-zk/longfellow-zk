// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{EvaluationDomain, PackingExtension, ZkField},
    dual_packing::generic::{self, PackingProof},
    polygero::{PolygeroParam, PolygeroVerifier},
    proto::polygero::{PolygeroCommitment, PolygeroProof},
    random::Transcript,
};
pub(in crate::runtime::zk_v2) struct CommitmentVerifier<
    F: crate::runtime::algebra::PackingField,
    X: PackingExtension<Ambient = F>,
> {
    pub backend: PackingCommitment<F, X>,
    polygero: PolygeroVerifier,
}
impl<F: crate::runtime::algebra::PackingField, X: PackingExtension<Ambient = F>>
    CommitmentVerifier<F, X>
{
    pub fn new(backend: PackingCommitment<F, X>, param: PolygeroParam) -> Self {
        Self {
            backend,
            polygero: PolygeroVerifier::new(param),
        }
    }
    pub fn receive(&mut self, root: &PolygeroCommitment, id: &[u8; 32], t: &mut Transcript)
    where F: crate::core::algebra::SerializableField {
        self.backend.bind(t, id);
        self.polygero.receive_commitment(root, t);
    }
    pub fn verify<const W: usize, D: EvaluationDomain<W, F>>(
        &self,
        statement: CommitmentStatement<F::E>,
        messages: (
            &PackingProof<F::E>,
            &PolygeroCommitment,
            &PolygeroProof<F::E>,
        ),
        id: &[u8; 32],
        t: &mut Transcript,
        domain: &D,
    ) -> Result<(), String>
    where
        F: ZkField<W>,
    {
        let (packing, root, proof) = messages;
        let rows = generic::verify(&self.backend.parameters, &statement.claim, packing, id, t)?;
        let binding = super::super::transcript::statement_digest(t);
        let (native_a, native_b) = self.backend.authenticate::<W>(statement, &rows)?;
        drop(rows);
        self.polygero
            .verify(
                &native_b,
                root,
                proof,
                &native_a,
                &binding,
                t,
                domain,
                self.backend.parameters.field(),
            )
            .map_err(|e| e.to_string())
    }
}
