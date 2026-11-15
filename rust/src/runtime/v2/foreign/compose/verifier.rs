// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's side of the composition driver.
use super::*;
use crate::runtime::v2::{
    proto::composed::ComposedProof,
    transcript::Transcript,
    zk::{self, joint::FrontendPart, split, CircuitInput},
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
        let split_part = FrontendPart::new(&self.split, &[self.split_circuit], split_public)?;
        let host_part = FrontendPart::new(
            &self.host,
            &[self.host_circuit, self.mode.fragment()],
            host_public,
        )?;
        let mut joint = param.receive(&proof.commitment, proof.fingerprints.clone(), transcript);

        // Split frontend, then the split of its input equation.
        let mut ts = joint.bound(&split_part);
        let claim = zk::reduce_split(&mut ts, &proof.split.sumcheck_proof, &self.split_ctx)?;
        let eta = split::transcript::eta(&mut ts, fs);
        let split = claim.receive(&mut ts, eta, &proof.mu, fs)?;

        // Adapter rounds, then the host frontend with the mode's fragment.
        let mut ta = joint.bound(&self.mode);
        let conversion = M::draw_conversion(&mut ta, fs);
        let leaves = M::verify(&mut ta, &split.foreign, &proof.message, conversion, fs, fh)?;
        let statement_host = zk::reduce(
            &mut joint.bound(&host_part),
            &proof.host,
            &leaves,
            &self.host_ctx,
        )?;
        Ok(joint
            .authenticate(&proof.polygero, (statement_host, (split.statement, ())))?
            .into_transcript())
    }
}
