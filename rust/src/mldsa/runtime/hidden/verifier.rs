// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    mldsa::{proto::MlDsaParams, runtime::binary::BinaryParticipant},
    runtime::{
        algebra::{
            fp24_ext6::RuntimeFp24Ext6 as AF, range_interpolation::BinaryInterpolatorFactory,
        },
        v2::{
            foreign::adapter::exact::ExactMode,
            zk::{
                joint::{FrontendPart, JointParam},
                split::pure,
                write_joint_geometry,
            },
        },
    },
};
pub fn verify<P: MlDsaParams>(c: &Circuits, context: &[u8], bytes: &[u8]) -> Result<(), String> {
    let f = Gf2_128Field::new();
    let af = AF::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let link = Link::new(c)?;
    let binary = link.host(c, &domain)?;
    let native = link.native(c, &CrtInterpolatorFactory)?;
    let params = JointParam::new((binary.participant(&domain)?, ()))?;
    let native_part = FrontendPart::new(&native, &[&c.arithmetic], &[])?;
    let g = proto::geometry(c, binary.geometry(), &native);
    let (tail, proof) = proto::Proof::<Gf2_128Field>::read(bytes, &g, &f)?;
    if !tail.is_empty() {
        return Err("hidden proof trailing bytes".into());
    }
    let initial_transcript = transcript::start::<P>(c, context, |h| {
        binary.write_layout(h);
        native_part.write_layout(h);
        link.map.write_layout(h);
        link.mode.write_layout(h);
        write_joint_geometry(h, c.config);
    });
    let mut joint = params.receive(
        &proof.commitment,
        (proof.fingerprints.clone(), ()),
        initial_transcript,
    );

    let pending = pure::verifier::reduce(&mut joint.bound(&native_part), &proof.native)?;
    let linear = pending.batch_linear(&mut joint.bound(&native_part))?;
    let claim = link.map.modular_claim(&linear, &basis(&af), &af)?;
    let leaves = ExactMode::verify(&mut joint.bound(&link.mode), &claim, &proof.masked, &af, &f)?;
    let gamma = transcript::gamma(&mut joint.bound(&binary).transcript());

    let statement = BinaryParticipant::reduce(
        &mut joint.bound(&binary),
        &c.binary,
        link.mode.fragment(),
        &gamma,
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
