// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use std::sync::Arc;

use super::super::{binary::BinaryParticipant, *};
use crate::runtime::{
    algebra::range_interpolation::BinaryInterpolatorFactory,
    v2::{
        foreign::adapter::exact::ExactMode,
        zk::{joint::JointParam, write_joint_geometry},
    },
};
pub(in crate::mldsa::runtime) fn verify<P: MlDsaParams>(
    c: &Circuits,
    encoded_key: &[u8],
    context: &[u8],
    bytes: &[u8],
) -> Result<(), String> {
    let f = BF::new();
    let af = RuntimeFp24Ext6::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let link = Link::new::<P>(c)?;
    let mut binary = BinaryParticipant::new(
        &c.binary,
        link.mode.fragment(),
        link.mode.virtual_inputs(),
        c.config,
        &domain,
    )?;
    if let Some(source) = &c.source {
        binary = binary.with_simd(Arc::clone(source), &domain)?;
    }
    let params = JointParam::new((binary.participant(&domain)?, ()))?;
    let (remaining, proof) = proto::Proof::read(bytes, &proto::geometry(c, binary.geometry()), &f)?;
    if !remaining.is_empty() {
        return Err("trailing ML-DSA proof bytes".into());
    }
    let key = public_key::<P>(encoded_key)?;
    let initial_transcript = transcript::start::<P>(c, &key, context, |h| {
        binary.write_layout(h);
        link.mode.write_layout(h);
        write_joint_geometry(h, c.config);
    });
    let mut joint = params.receive(
        &proof.commitment,
        (proof.fingerprints.clone(), ()),
        initial_transcript,
    );
    let claim = link.claim(
        transcript::projections::<P>(&key, &mut joint.bound(&binary).transcript()),
        &af,
    );
    let leaves = ExactMode::verify(&mut joint.bound(&link.mode), &claim, &proof.masked, &af, &f)?;

    let statement = BinaryParticipant::reduce(
        &mut joint.bound(&binary),
        &c.binary,
        link.mode.fragment(),
        &[],
        &proof.binary,
        proof.simd.as_ref(),
        &leaves,
    )?;
    let statements = (statement, ());
    let authenticated = joint.finish(statements, proof)?;
    authenticated
        .check_seal()
        .map(|_| ())
        .map_err(str::to_owned)
}
