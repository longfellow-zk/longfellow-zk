// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's side of the composition driver.
use super::*;
use crate::runtime::{
    random::RandomEngine,
    v2::{
        proto::{composed::ComposedProof, dual_packing::PackingProof, zk::CircuitProof},
        transcript::Transcript,
        zk::{split, CircuitInput},
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
        rng: &mut impl RandomEngine,
    ) -> Result<(ComposedProof<H, Host, W, F, M::Message>, Transcript), String> {
        let (fh, fs) = (self.host_ctx.field(), self.split_ctx.field());
        // The split mask R and the mode's pads fill the reserved suffix.
        let mask = rng.elt_field(fs);
        let pads = self.mode.sample_pads(rng);
        let mut reserved = self.suffix.witness();
        let bytes = fs.to_bytes(&mask);
        reserved.set(
            self.mask,
            (0..self.mask.width).map(|r| (bytes[r / 8] >> (r % 8)) & 1 != 0),
        )?;
        self.mode.write_pads(&pads, &mut reserved)?;
        host_private.extend(reserved.into_bits());

        let param = self.param()?;
        let (state_host, w_host) = self.host.prepare(host_private, rng)?;
        let (state_split, w_split) = self.split.prepare_split(split_private, Some(mask), rng)?;
        let (mut joint, commitment, fingerprints) =
            param.commit((w_host, (w_split, ())), transcript, rng)?;
        let mut t = joint.transcript();

        // Split frontend, then the split of its input equation.
        let (sumcheck, pending) = self.split.prove_split(
            self.split_circuit,
            split_public,
            state_split,
            &mut t,
            &self.split_ctx,
        )?;
        let eta = split::transcript::eta(&mut t, fs);
        let mu = self.split.split_message(&pending, &eta, fs)?;
        split::transcript::absorb_mu(&mut t, &mu, fs);
        let claim = self.split.foreign_claim(&pending.claim, &eta, &mu, fs)?;

        // Adapter rounds, then the host frontend with the mode's fragment.
        let values = self.split.foreign_values(&pending)?;
        let (message, leaves) = self.mode.prove(&claim, &values, &pads, &mut t, fs, fh)?;
        let (host, statement_host) = self.host.prove_virtual(
            self.host_circuit,
            host_public,
            state_host,
            &[self.mode.fragment()],
            &leaves,
            &mut t,
            &self.host_ctx,
        )?;
        let statement_split = self.split.split_statement(&pending.claim, &eta, &mu, fs)?;
        let (polygero, transcript) =
            joint.prove(&param, (statement_host, (statement_split, ())))?;
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
