// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use std::sync::Arc;

use super::super::{binary::BinaryParticipant, *};
use crate::{
    core::algebra::SupportsU64Conversions,
    mldsa::runtime::reference::ConcreteInstance,
    runtime::{
        algebra::range_interpolation::BinaryInterpolatorFactory,
        random::PrivateRandom,
        v2::{
            foreign::adapter::exact::ExactMode,
            zk::{joint::JointParam, write_joint_geometry},
        },
    },
};
pub(in crate::mldsa::runtime) fn prove<P: MlDsaParams>(
    c: &Circuits,
    encoded_key: &[u8],
    instance: &ConcreteInstance<P>,
    context: &[u8],
    rng: &mut impl PrivateRandom,
) -> Result<Vec<u8>, String> {
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
    let key = public_key::<P>(encoded_key)?;
    let initial_transcript = transcript::start::<P>(c, &key, context, |h| {
        binary.write_layout(h);
        link.mode.write_layout(h);
        write_joint_geometry(h, c.config);
    });
    // Signature witness, then the reserved suffix: one pad per quotient.
    let mut bits = witness::binary_inputs(instance, c.keccak);
    if bits.len() != c.binary.raw.ninput {
        return Err("ML-DSA witness width".into());
    }
    let values: Vec<_> = link
        .groups
        .iter()
        .map(|g| {
            let word = bits[g.start()..g.end()]
                .iter()
                .rev()
                .fold(0u64, |v, &b| v << 1 | u64::from(b));
            af.u64_to_element(word)
        })
        .collect();
    let pads = link.mode.sample_pads(rng);
    let mut reserved = link.suffix.witness();
    link.mode.write_pads(&pads, &mut reserved)?;
    bits.extend(reserved.into_bits());
    let (state, cells) = binary.prepare(&bits, rng)?;
    let (mut joint, commitment, fingerprints) =
        params.commit((cells, ()), initial_transcript, rng)?;
    // Six projections, then the adapter's masked quotients and leaves.
    let claim = link.claim(
        transcript::projections::<P>(&key, &mut joint.bound(&binary).transcript()),
        &af,
    );
    let (masked, leaves) =
        ExactMode::prove(&mut joint.bound(&link.mode), &claim, &values, pads, &af, &f)?;

    let (proof, simd, statement) = BinaryParticipant::prove(
        &mut joint.bound(&binary),
        &c.binary,
        link.mode.fragment(),
        &[],
        bits,
        state,
        &leaves,
    )?;
    let statements = (statement, ());
    let (opening, sealed_transcript) = joint.finish(statements)?;
    proto::Proof {
        simd,
        masked,
        commitment,
        fingerprints: fingerprints.0,
        binary: proof,
        polygero: opening,
    }
    .write(
        &proto::geometry(c, binary.geometry()),
        &f,
        sealed_transcript,
    )
    .map(|p| p.into_bytes())
}
