// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's side of the composition driver.
use super::*;
use crate::runtime::v2::{
    proto::composed::ComposedProof,
    transcript::{Opened, SetupMessage, Transcript},
    zk::{self, joint, split},
};

impl<const W: usize, F, DH, DS, M, I> ComposedStatement<'_, W, F, DH, DS, M, I>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
    M: AdapterMode<F>,
    I: SetupMessage,
{
    /// Reduce both circuits of the composition statement `session` opened
    /// with and authenticate the joint opening. This is not complete
    /// verification: the caller must check the complete proof's final seal
    /// on the returned transcript, as `run_mdoc_verifier` does.
    #[doc = include_str!("verifier_compile_fail.md")]
    #[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
    pub(crate) fn reduce_and_authenticate(
        session: Opened<'_, Self>,
        proof: &ComposedProof<H, Host, W, F, M::Message>,
    ) -> Result<Transcript, String> {
        let (this, transcript) = session.into_parts();
        let c = this.composition;
        let (fh, fs) = (c.host_ctx.field(), c.split_ctx.field());
        let param = c.param()?;
        let mut joint = param.receive(&proof.commitment, proof.fingerprints.clone(), transcript);

        // Split frontend from the top weights after the fingerprint
        // responses, then the split of its input equation. eta extends the
        // frontend's last combine answer.
        let mut ts = joint.bound(&this.split);
        let top_split = joint::top_weights(&mut ts)?;
        let claim = zk::reduce_split(&mut ts, &proof.split, top_split, &c.split_ctx)?;
        let eta = split::transcript::eta(&mut ts, fs);
        let split = claim.receive(&mut ts, eta, &proof.mu, fs)?;

        // Adapter rounds, then the host frontend with the mode's fragment,
        // from the top weights after the adapter's masked quotients.
        let mut ta = joint.bound(&c.mode);
        let conversion = M::draw_conversion(&mut ta, fs);
        let leaves = M::verify(&mut ta, &split.foreign, &proof.message, conversion, fs, fh)?;
        let mut th = joint.bound(&this.host);
        let top_host = joint::top_weights(&mut th)?;
        let statement_host = zk::reduce(&mut th, &proof.host, top_host, &leaves, &c.host_ctx)?;
        // The batching weights follow the host frontend's last message.
        let statements = (statement_host, (split.statement, ()));
        let batch = joint.weights(statements);
        Ok(joint
            .authenticate(batch, &proof.polygero)?
            .into_transcript())
    }
}
