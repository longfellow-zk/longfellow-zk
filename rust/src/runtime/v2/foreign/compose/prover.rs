// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's side of the composition driver.
use super::*;
#[cfg(test)]
use crate::runtime::v2::transcript::cheat;
use crate::runtime::{
    random::PrivateRandom,
    v2::{
        proto::composed::ComposedProof,
        transcript::{Opened, SetupMessage, Transcript},
        zk,
    },
};

impl<const W: usize, F, DH, DS, M, I> ComposedStatement<'_, W, F, DH, DS, M, I>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
    M: AdapterMode<F>,
    I: SetupMessage,
{
    /// Prove both circuits of the composition statement `session` opened
    /// with. `host_private` is the host circuit's own private input;
    /// this appends R and the mode's pads.
    #[allow(clippy::type_complexity)]
    pub(crate) fn prove(
        session: Opened<'_, Self>,
        mut host_private: Vec<CircuitInput<Host>>,
        split_private: Vec<CircuitInput<F>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(ComposedProof<H, Host, W, F, M::Message>, Transcript), String> {
        let (this, transcript) = session.into_parts();
        let c = this.composition;
        let (fh, fs) = (c.host.field(), c.split.field());
        // The split mask R and the mode's pads fill the reserved suffix.
        let mask = rng.elt_field(fs);
        let pads = c.mode.sample_pads(rng);
        let mut reserved = c.suffix.witness();
        let bytes = fs.to_bytes(&mask);
        reserved.set(
            c.mask,
            (0..c.mask.width()).map(|r| (bytes[r / 8] >> (r % 8)) & 1 != 0),
        )?;
        c.mode.write_pads(&pads, &mut reserved)?;
        host_private.extend(reserved.into_bits());
        // Tests only (`cheat::cheating_from_host_bits`): the foreign values as
        // the host's bits give them, not as the split frontend has them.
        #[cfg(test)]
        let host_values = cheat::from_host_bits().then(|| c.host_values(&host_private));

        let param = c.param()?;
        let (state_host, w_host) = c.host.prepare(host_private, rng)?;
        let (state_split, w_split) = c.split.prepare(split_private, mask, rng)?;
        let (mut joint, commitment, fingerprints) =
            param.commit((w_host, (w_split, ())), transcript, rng)?;

        // Split frontend, whose top weights follow the fingerprint responses,
        // then the split of its input equation, whose eta extends the
        // frontend's last combine answer.
        let mut ts = joint.bound(&this.split);
        #[cfg_attr(not(test), allow(unused_mut))]
        let (split_sumcheck, mut pending) = zk::prove_split(&mut ts, state_split)?;
        #[cfg(test)]
        for (i, v) in host_values.into_iter().flatten() {
            pending.values[i] = v;
        }
        let values = c.split.foreign_values(&pending);
        let (mu, split) = pending.open(&mut ts)?;

        // Adapter rounds, whose conversion pair follows the split message,
        // then the host frontend with the mode's fragment, whose top weights
        // follow the adapter's masked quotients.
        let mut ta = joint.bound(&c.mode);
        let (message, leaves) = M::prove(&mut ta, &split.foreign, &values, pads, fs, fh)?;
        let mut th = joint.bound(&this.host);
        let (host, statement_host) = zk::prove(&mut th, state_host, &leaves)?;
        // The opening follows the host frontend's last message.
        let equations = (statement_host, (split.statement, ()));
        let (polygero, transcript) = joint.finish(&param, equations)?;
        Ok((
            ComposedProof {
                commitment,
                fingerprints,
                split: split_sumcheck,
                mu,
                message,
                host,
                polygero,
            },
            transcript,
        ))
    }
}

#[cfg(test)]
impl<const W: usize, F, DH, DS, M> Composition<'_, W, F, DH, DS, M>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
{
    /// The split's foreign values as the host's private bits `host_private`
    /// give them, by value index: the integer of each group, least
    /// significant bit first.
    fn host_values(&self, host_private: &[bool]) -> Vec<(usize, F::E)> {
        let (f, npublic) = (self.split.field(), self.host_circuit.raw.npublic_input);
        self.split
            .map_for_test()
            .entries()
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match s {
                Storage::Foreign(g) => {
                    let mut v = f.zero();
                    for r in (0..g.width()).rev() {
                        v = f.addf(&v, &v);
                        if host_private[g.bit(r) - npublic] {
                            v = f.addf(&v, &f.one());
                        }
                    }
                    Some((i, v))
                }
                Storage::Native(_) => None,
            })
            .collect()
    }
}
