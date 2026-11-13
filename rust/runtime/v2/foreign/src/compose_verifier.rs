// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's side of the composition driver.
use super::*;
use crate::runtime::v2::{
    proto::composed::ComposedProof,
    transcript::Transcript,
    zk::{split, CircuitInput},
};

impl<const W: usize, F, DH, DS, M> Composition<'_, W, F, DH, DS, M>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
    M: AdapterMode<F>,
{
    /// Reduce both circuits and authenticate the joint opening. `transcript`
    /// already binds the application statement. The returned transcript must
    /// still check the complete proof's final seal.
    pub fn verify(
        &self,
        host_public: &[CircuitInput<Host>],
        split_public: &[CircuitInput<F>],
        proof: &ComposedProof<H, Host, W, F, M::Message>,
        transcript: Transcript,
    ) -> Result<Transcript, String> {
        let (fh, fs) = (self.host_ctx.field(), self.split_ctx.field());
        let param = self.param()?;
        let mut joint = param.receive(&proof.commitment, proof.fingerprints.clone(), transcript);
        let mut t = joint.transcript();

        // Split frontend, then the split of its input equation.
        let claim = self.split.reduce_split(
            self.split_circuit,
            split_public,
            &proof.split.sumcheck_proof,
            &mut t,
            &self.split_ctx,
        )?;
        let eta = split::transcript::eta(&mut t, fs);
        split::transcript::absorb_mu(&mut t, &proof.mu, fs);
        let foreign = self.split.foreign_claim(&claim, &eta, &proof.mu, fs)?;

        // Adapter rounds, then the host frontend with the mode's fragment.
        let leaves = self.mode.verify(&foreign, &proof.message, &mut t, fs, fh)?;
        let statement_host = self.host.reduce(
            &[self.host_circuit, self.mode.fragment()],
            host_public,
            &proof.host,
            &leaves,
            &mut t,
            &self.host_ctx,
        )?;
        let statement_split = self.split.split_statement(&claim, &eta, &proof.mu, fs)?;
        Ok(joint
            .authenticate(&proof.polygero, (statement_host, (statement_split, ())))?
            .into_transcript())
    }
}
