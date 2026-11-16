// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The verifier's side of the composition driver.
use super::*;
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::v2::{
        proto::{
            composed::ComposedProof,
            polygero::{FieldProof, JointPolygeroProof},
        },
        transcript::{Bound, Opened, SetupMessage, Unverified},
        zk::{self, Authenticated, JointOpening},
    },
};

/// The field proofs of a composed body's joint opening: the host's, then the
/// split participant's.
type Bodies<H, S> = (FieldProof<ElementOf<H>>, (FieldProof<ElementOf<S>>, ()));

impl<F, DH, DS, M, I> ComposedStatement<'_, F, DH, DS, M, I>
where
    F: ZkField + PackingField,
    DH: EvaluationDomain<Host>,
    DS: EvaluationDomain<F>,
    M: AdapterMode<F>,
    I: SetupMessage,
{
    /// Reduce both circuits of the composition statement `session` opened
    /// with on the composed body of `proof`, the complete proof, and
    /// authenticate its joint opening. This is not complete verification:
    /// the caller must check the seal of `proof`, which the returned
    /// `Authenticated` keeps, as `run_mdoc_verifier` does.
    #[doc = include_str!("verifier_compile_fail.md")]
    pub(crate) fn reduce_and_authenticate<'p, P>(
        session: Opened<'_, Self>,
        proof: Unverified<'p, P>,
    ) -> Result<Authenticated<'p, P>, String>
    where
        P: AsRef<ComposedProof<Host, F, M::Message>> + JointOpening<Bodies<Host, F>>,
    {
        let body = (*proof).as_ref();
        let (this, transcript) = session.into_parts();
        let c = this.composition;
        let (fh, fs) = (c.host.field(), c.split.field());
        let param = c.param()?;
        let mut joint = param.receive(&body.commitment, body.fingerprints.clone(), transcript);

        // Split frontend, whose top weights follow the fingerprint responses,
        // then the split of its input equation, whose eta extends the
        // frontend's last combine answer.
        let mut ts = joint.bound(&this.split);
        let claim = zk::reduce_split(&mut ts, &body.split)?;
        let split = claim.receive(&mut ts, &body.mu)?;

        // Adapter rounds, whose conversion pair follows the split message,
        // then the host frontend with the mode's fragment, whose top weights
        // follow the adapter's masked quotients.
        let mut ta = joint.bound(&c.mode);
        let leaves = M::verify(&mut ta, &split.foreign, &body.message, fs, fh)?;
        let mut th = joint.bound(&this.host);
        let statement_host = zk::reduce(&mut th, &body.host, &leaves)?;
        // The opening follows the host frontend's last message.
        let equations = (statement_host, (split.statement, ()));
        joint.finish(equations, proof)
    }
}
impl<'s, 'a: 's, F, DH, DS, M, I> Opened<'s, ComposedStatement<'a, F, DH, DS, M, I>>
where
    F: ZkField + PackingField,
    DH: EvaluationDomain<Host>,
    DS: EvaluationDomain<F>,
{
    /// The session, bound to the geometry its statement wrote, which the
    /// proof is parsed against (transcript I2).
    pub(crate) fn geometry(&mut self) -> Bound<'_, ComposedGeometry> {
        self.bound(|s| &s.geometry)
    }
}

/// The joint opening of every composed body, with or without an
/// application's envelope.
impl<H: SerializableField, S: SerializableField, M> JointOpening<Bodies<H, S>>
    for ComposedProof<H, S, M>
{
    fn opening(&self) -> &JointPolygeroProof<Bodies<H, S>> {
        &self.polygero
    }
}
