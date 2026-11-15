// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's side of the composition driver.
use super::*;
use crate::runtime::{
    random::PrivateRandom,
    v2::{
        proto::composed::ComposedProof,
        transcript::{Opened, Statement, Transcript},
        zk::{self, joint, split},
    },
};

impl<const W: usize, F, DH, DS, M> ComposedStatement<'_, W, F, DH, DS, M>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
    M: AdapterMode<F>,
{
    /// Prove both circuits of the composition part of the statement `session`
    /// opened with. `host_private` is the host circuit's own private input;
    /// this appends R and the mode's pads.
    #[allow(clippy::type_complexity)]
    pub fn prove<S: Statement + AsRef<Self> + ?Sized>(
        session: Opened<'_, S>,
        mut host_private: Vec<CircuitInput<Host>>,
        split_private: Vec<CircuitInput<F>>,
        rng: &mut impl PrivateRandom,
    ) -> Result<(ComposedProof<H, Host, W, F, M::Message>, Transcript), String> {
        let (statement, transcript) = session.into_parts();
        let this: &Self = statement.as_ref();
        let c = this.composition;
        let (fh, fs) = (c.host_ctx.field(), c.split_ctx.field());
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

        let param = c.param()?;
        let (state_host, w_host) = c.host.prepare(host_private, rng)?;
        let (state_split, w_split) = c.split.prepare_split(split_private, Some(mask), rng)?;
        let (mut joint, commitment, fingerprints) =
            param.commit((w_host, (w_split, ())), transcript, rng)?;

        // Split frontend from the top weights after the fingerprint
        // responses, then the split of its input equation. eta extends the
        // frontend's last combine answer.
        let mut ts = joint.bound(&this.split);
        let top_split = joint::top_weights(&mut ts)?;
        let (split_sumcheck, pending) =
            zk::prove_split(&mut ts, state_split, top_split, &c.split_ctx)?;
        let values = c.split.foreign_values(&pending)?;
        let eta = split::transcript::eta(&mut ts, fs);
        let (mu, split) = pending.open(&mut ts, eta, fs)?;

        // Adapter rounds, then the host frontend with the mode's fragment,
        // from the top weights after the adapter's masked quotients.
        let mut ta = joint.bound(&c.mode);
        let conversion = M::draw_conversion(&mut ta, fs);
        let (message, leaves) =
            M::prove(&mut ta, &split.foreign, &values, &pads, conversion, fs, fh)?;
        let mut th = joint.bound(&this.host);
        let top_host = joint::top_weights(&mut th)?;
        let (host, statement_host) =
            zk::prove(&mut th, state_host, top_host, &leaves, &c.host_ctx)?;
        let (polygero, transcript) =
            joint.prove(&param, (statement_host, (split.statement, ())))?;
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
