// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's encoding of a complete v2 proof.
use super::{CircuitProof, ZkProof, ZkProofGeometry};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::RuntimeField,
        v2::transcript::{EncodedProof, Transcript},
    },
};

impl<const W: usize, F: RuntimeField<W> + SerializableField> ZkProof<W, F> {
    /// `LFV9`, then the body in send order: root, fingerprints, sumcheck,
    /// packing, response; then the terminal rows, nonces and frontier (its
    /// count, then its digests).
    fn write_body(&self, buf: &mut Vec<u8>, g: &ZkProofGeometry, f: &F) -> std::io::Result<()> {
        buf.extend_from_slice(&Self::MAGIC);
        buf.extend_from_slice(&self.com.root.data);
        self.fingerprints.write(buf, f);
        CircuitProof::<W, F>::write_parts(&self.sumcheck_proof, &self.packing, buf, &g.circuit, f)?;
        let geom = &g.polygero();
        self.com_proof.write_to_buf(
            buf,
            g.config.t,
            g.config.n,
            |b, out| b.0.write_response(out, geom, f),
            |b, out| b.0.write_rows(out, geom, f),
        )
    }
    /// The complete proof: the body, sealed with `transcript` (transcript
    /// I10). Only `ZkProver::prove`, which owns the session, seals one.
    pub(crate) fn write(
        &self,
        g: &ZkProofGeometry,
        f: &F,
        transcript: Transcript,
    ) -> std::io::Result<EncodedProof> {
        let mut b = Vec::new();
        self.write_body(&mut b, g, f)?;
        Ok(transcript.append_final_seal(b))
    }
}
