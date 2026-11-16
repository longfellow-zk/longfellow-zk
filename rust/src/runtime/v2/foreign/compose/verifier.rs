// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's side of the composition driver.
use super::*;
use crate::runtime::v2::{
    proto::composed::ComposedProof,
    transcript::{Bound, Opened, SetupMessage},
    zk::{self, Authenticated},
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
    /// with the returned `Authenticated`, as `run_mdoc_verifier` does.
    #[doc = include_str!("verifier_compile_fail.md")]
    pub(crate) fn reduce_and_authenticate(
        session: Opened<'_, Self>,
        proof: &ComposedProof<H, Host, W, F, M::Message>,
    ) -> Result<Authenticated, String> {
        let (this, transcript) = session.into_parts();
        let c = this.composition;
        let (fh, fs) = (c.host.field(), c.split.field());
        let param = c.param()?;
        let mut joint = param.receive(&proof.commitment, proof.fingerprints.clone(), transcript);

        // Split frontend, whose top weights follow the fingerprint responses,
        // then the split of its input equation, whose eta extends the
        // frontend's last combine answer.
        let mut ts = joint.bound(&this.split);
        let claim = zk::reduce_split(&mut ts, &proof.split)?;
        let split = claim.receive(&mut ts, &proof.mu)?;

        // Adapter rounds, whose conversion pair follows the split message,
        // then the host frontend with the mode's fragment, whose top weights
        // follow the adapter's masked quotients.
        let mut ta = joint.bound(&c.mode);
        let leaves = M::verify(&mut ta, &split.foreign, &proof.message, fs, fh)?;
        let mut th = joint.bound(&this.host);
        let statement_host = zk::reduce(&mut th, &proof.host, &leaves)?;
        // The opening follows the host frontend's last message.
        let equations = (statement_host, (split.statement, ()));
        joint.finish(equations, &proof.polygero)
    }
}
impl<'s, 'a: 's, const W: usize, F, DH, DS, M, I>
    Opened<'s, ComposedStatement<'a, W, F, DH, DS, M, I>>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
{
    /// The session, bound to the geometry its statement wrote, which the
    /// proof is parsed against (transcript I2).
    pub(crate) fn geometry(&mut self) -> Bound<'_, ComposedGeometry> {
        self.bound(|s| &s.geometry)
    }
}
