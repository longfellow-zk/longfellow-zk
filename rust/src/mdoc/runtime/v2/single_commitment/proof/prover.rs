// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::transcript::{EncodedProof, Transcript};
impl Proof {
    pub(in crate::mdoc::runtime::v2::single_commitment) fn write(
        &self,
        g: &ProofGeometry,
        f: &Gf2_128Field,
        p: &P256Field,
        t: Transcript,
    ) -> Result<EncodedProof, String> {
        g.fixed_len(f, p)
            .ok_or("single-commitment proof geometry")?;
        let mut out = Self::MAGIC.to_vec();
        out.extend(self.commitment.root.data);
        self.fingerprints.write(&mut out, f);
        self.signature
            .write_to_buf(&mut out, &g.signature, p)
            .map_err(|e| e.to_string())?;
        for q in &self.masked {
            q.write(&mut out);
        }
        self.binary
            .write_to_buf(&mut out, &g.binary, f)
            .map_err(|e| e.to_string())?;
        self.polygero
            .write_to_buf::<std::io::Error>(
                &mut out,
                g.config.t,
                g.config.n,
                |b, buf| b.0.write_response(buf, &g.polygero, f),
                |b, buf| b.0.write_rows(buf, &g.polygero, f),
            )
            .map_err(|e| e.to_string())?;
        Ok(t.append_final_seal(out))
    }
}
