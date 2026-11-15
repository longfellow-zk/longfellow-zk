// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    proto::{polygero::codec::checked_body, read_bytes_32, Digest},
    transcript::{Bound, Unverified, SEAL_BYTES},
    zk::JointOpening,
};

impl JointOpening<(FieldProof<Gf2_128>, ())> for Proof {
    fn opening(&self) -> &JointPolygeroProof<(FieldProof<Gf2_128>, ())> {
        &self.polygero
    }
}
impl Proof {
    pub(in crate::mdoc::runtime::v2::single_commitment) fn read<'a>(
        bytes: &'a [u8],
        bound: &Bound<'_, ProofGeometry>,
        f: &Gf2_128Field,
        p: &P256Field,
    ) -> Result<Unverified<'a, Self>, String> {
        let g = bound.part();
        let fixed = g
            .fixed_len(f, p)
            .ok_or("single-commitment proof geometry")?;
        let mut remaining = checked_body(bytes, Self::MAGIC.len(), fixed, g.config.t, g.config.n)
            .map_err(|e| e.to_string())?;
        if bytes.get(..Self::MAGIC.len()) != Some(Self::MAGIC) {
            return Err("single-commitment mdoc proof version".into());
        }
        let commitment = PolygeroCommitment {
            root: Digest {
                data: read_bytes_32(&mut remaining).map_err(|e| e.to_string())?,
            },
        };
        let fingerprints =
            FingerprintResponse::read(&mut remaining, f).map_err(|e| e.to_string())?;
        let signature =
            SumcheckProof::read(&mut remaining, &g.signature, p).map_err(|e| e.to_string())?;
        let masked = [
            MaskedWord::read(&mut remaining)?,
            MaskedWord::read(&mut remaining)?,
        ];
        let binary = CircuitProof::read(&mut remaining, &g.binary, f).map_err(|e| e.to_string())?;
        let polygero = JointPolygeroProof::read::<std::io::Error>(
            &mut remaining,
            g.config.t,
            g.config.n,
            |r| Ok((FieldProof::read_response(r, &g.polygero, f)?, ())),
            |b, r| b.0.read_rows(r, &g.polygero, f),
        )
        .map_err(|e| e.to_string())?;
        let mut seal = &bytes[bytes.len() - SEAL_BYTES..];
        Unverified::decoded(
            Self {
                commitment,
                fingerprints,
                signature,
                masked,
                binary,
                polygero,
            },
            bytes,
            &mut seal,
        )
        .map_err(|e| e.to_string())
    }
}
