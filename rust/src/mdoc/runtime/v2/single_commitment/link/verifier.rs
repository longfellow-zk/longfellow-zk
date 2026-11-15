// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{super::proof::Proof, *};
use crate::{
    core::algebra::AlgebraicField,
    runtime::v2::{
        transcript::{Bound, Opened, Unverified},
        zk::{self, Authenticated},
    },
};
impl<DH> Link<'_, DH>
where DH: EvaluationDomain<Gf2_128Field>
{
    pub(in crate::mdoc::runtime::v2::single_commitment) fn verify<'p>(
        &self,
        proof: Unverified<'p, Proof>,
        session: Opened<'_, super::Statement<'_, DH>>,
    ) -> Result<Authenticated<'p, Proof>, String> {
        let (statement, t) = session.into_parts();
        if !std::ptr::eq(statement.link, self) {
            return Err("single-commitment statement belongs to another link".into());
        }
        let param = self.param()?;
        let mut joint = param.receive(&proof.commitment, (proof.fingerprints.clone(), ()), t);
        let mut ts = joint.bound(&statement.native);
        let pending = zk::split::pure::verifier::reduce(&mut ts, &proof.signature)?;
        let linear = pending.batch_linear(&mut ts)?;
        let claim =
            self.map
                .modular_claim(&linear, &[self.native.field().one()], self.native.field())?;
        let mut ta = joint.bound(&self.mode);
        let leaves = Mode::verify(
            &mut ta,
            &claim,
            &proof.masked,
            self.native.field(),
            self.host.field(),
        )?;
        let mut th = joint.bound(&statement.host);
        let host_linear = zk::reduce(&mut th, &proof.binary, &leaves)?;
        let statements = (host_linear, ());
        joint.finish(statements, proof)
    }
}

impl<'s, 'a: 's, DH> Opened<'s, super::Statement<'a, DH>>
where DH: EvaluationDomain<Gf2_128Field>
{
    pub(in crate::mdoc::runtime::v2::single_commitment) fn geometry(
        &mut self,
    ) -> Bound<'_, ProofGeometry> {
        self.bound(|s| &s.geometry)
    }
}
