// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{super::proof::Proof, *};
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        random::PrivateRandom,
        v2::{
            transcript::{Opened, Transcript},
            zk::{self, CircuitInput},
        },
    },
};
impl<DH> Link<'_, DH>
where DH: EvaluationDomain<Gf2_128Field>
{
    pub(in crate::mdoc::runtime::v2::single_commitment) fn prove(
        &self,
        mut private: Vec<CircuitInput<Gf2_128Field>>,
        sig_private: Vec<CircuitInput<P256Field>>,
        session: Opened<'_, super::Statement<'_, DH>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(Proof, Transcript), String> {
        let (statement, t) = session.into_parts();
        if !std::ptr::eq(statement.link, self) {
            return Err("single-commitment statement belongs to another link".into());
        }
        let f = self.host.field();
        let p = self.native.field();
        let native_state = self.native.prepare(sig_private, rng)?;
        let encoded_values =
            self.map
                .encode_values::<4, _>(native_state.values(), |value, _| *value, p)?;
        let mut reserved = self.suffix.witness();
        // encode_values checked every unsigned group bound before any bit is written.
        for (stored, value) in self.map.values().iter().zip(&encoded_values) {
            let group = stored[0].group;
            let bytes = p.to_bytes(value);
            if group.start() >= self.hash.raw.ninput {
                reserved.set(
                    group,
                    (0..group.width()).map(|bit| bytes[bit / 8] >> (bit % 8) & 1 != 0),
                )?;
            } else {
                let bit = *private
                    .get(group.start() - self.hash.raw.npublic_input)
                    .ok_or("single shared witness bit")?;
                if bit != (bytes[0] & 1 != 0) {
                    return Err("single shared witnesses disagree".into());
                }
            }
        }
        let pads = self.mode.sample_pads(rng);
        self.mode.write_pads(&pads, &mut reserved)?;
        private.extend(reserved.into_bits());
        let (host_state, cells) = self.host.prepare(private, rng)?;
        let param = self.param()?;
        let (mut joint, commitment, fingerprints) = param.commit((cells, ()), t, rng)?;
        let mut ts = joint.bound(&statement.native);
        let (signature, pending) = zk::split::pure::prover::prove(&mut ts, native_state)?;
        let linear = pending.claim.batch_linear(&mut ts)?;
        let claim = self.map.modular_claim(&linear, &[p.one()], p)?;
        let values = encoded_values;
        let mut ta = joint.bound(&self.mode);
        let (masked, leaves) = Mode::prove(&mut ta, &claim, &values, pads, p, f)?;
        let mut th = joint.bound(&statement.host);
        let (binary, host_linear) = zk::prove(&mut th, host_state, &leaves)?;
        let statements = (host_linear, ());
        let (polygero, transcript) = joint.finish(statements)?;
        Ok((
            Proof {
                commitment,
                fingerprints: fingerprints.0,
                signature,
                masked,
                binary,
                polygero,
            },
            transcript,
        ))
    }
}
