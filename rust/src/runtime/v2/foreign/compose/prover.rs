// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's side of the composition driver.
use super::*;
use crate::runtime::{
    random::PrivateRandom,
    v2::{
        proto::{composed::ComposedProof, dual_packing::PackingProof, zk::CircuitProof},
        transcript::Transcript,
        zk::{
            self,
            joint::{self, FrontendPart},
            split, CircuitInput,
        },
    },
};

impl<const W: usize, F, DH, DS, M> Composition<'_, W, F, DH, DS, M>
where
    F: ZkField<W> + PackingField,
    DH: EvaluationDomain<H, Host>,
    DS: EvaluationDomain<W, F>,
    M: AdapterMode<F>,
{
    /// Prove both circuits. `host_private` is the host circuit's own private
    /// input; this appends R and the mode's pads. `transcript` already binds
    /// the application statement.
    #[allow(clippy::type_complexity)]
    pub fn prove(
        &self,
        host_public: &[CircuitInput<Host>],
        mut host_private: Vec<CircuitInput<Host>>,
        split_public: &[CircuitInput<F>],
        split_private: Vec<CircuitInput<F>>,
        transcript: Transcript,
        rng: &mut impl PrivateRandom,
    ) -> Result<(ComposedProof<H, Host, W, F, M::Message>, Transcript), String> {
        let (fh, fs) = (self.host_ctx.field(), self.split_ctx.field());
        // The split mask R and the mode's pads fill the reserved suffix.
        let mask = rng.elt_field(fs);
        let pads = self.mode.sample_pads(rng);
        let mut reserved = self.suffix.witness();
        let bytes = fs.to_bytes(&mask);
        reserved.set(
            self.mask,
            (0..self.mask.width()).map(|r| (bytes[r / 8] >> (r % 8)) & 1 != 0),
        )?;
        self.mode.write_pads(&pads, &mut reserved)?;
        host_private.extend(reserved.into_bits());

        let param = self.param()?;
        let (state_host, w_host) = self.host.prepare(host_private, rng)?;
        let (state_split, w_split) = self.split.prepare_split(split_private, Some(mask), rng)?;
        let split_part = FrontendPart::new(&self.split, &[self.split_circuit], split_public)?;
        let host_part = FrontendPart::new(
            &self.host,
            &[self.host_circuit, self.mode.fragment()],
            host_public,
        )?;
        let (mut joint, commitment, fingerprints) =
            param.commit((w_host, (w_split, ())), transcript, rng)?;

        // Split frontend from the top weights after the fingerprint
        // responses, then the split of its input equation. eta extends the
        // frontend's last combine answer.
        let mut ts = joint.bound(&split_part);
        let top_split = joint::top_weights(&mut ts)?;
        let (sumcheck, pending) =
            zk::prove_split(&mut ts, state_split, top_split, &self.split_ctx)?;
        let values = self.split.foreign_values(&pending)?;
        let eta = split::transcript::eta(&mut ts, fs);
        let (mu, split) = pending.open(&mut ts, eta, fs)?;

        // Adapter rounds, then the host frontend with the mode's fragment,
        // from the top weights after the adapter's masked quotients.
        let mut ta = joint.bound(&self.mode);
        let conversion = M::draw_conversion(&mut ta, fs);
        let (message, leaves) =
            M::prove(&mut ta, &split.foreign, &values, &pads, conversion, fs, fh)?;
        let mut th = joint.bound(&host_part);
        let top_host = joint::top_weights(&mut th)?;
        let (host, statement_host) =
            zk::prove(&mut th, state_host, top_host, &leaves, &self.host_ctx)?;
        let (polygero, transcript) =
            joint.prove(&param, (statement_host, (split.statement, ())))?;
        Ok((
            ComposedProof {
                commitment,
                fingerprints,
                mu,
                message,
                host,
                split: CircuitProof {
                    sumcheck_proof: sumcheck,
                    packing: PackingProof::Direct,
                },
                polygero,
            },
            transcript,
        ))
    }
}
