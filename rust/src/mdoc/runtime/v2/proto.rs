// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The mdoc envelope: version `MDA7`, a composed proof body, the final seal.
use crate::runtime::v2::proto::composed::ComposedGeometry;
#[cfg(any(test, feature = "prover"))]
use crate::runtime::v2::transcript::EncodedProof;
#[cfg(any(test, feature = "prover", feature = "testonly"))]
use crate::runtime::v2::transcript::Transcript;
#[cfg(any(test, feature = "verifier"))]
use crate::runtime::v2::{
    proto::polygero::codec::checked_body,
    transcript::{Bound, Unverified, SEAL_BYTES},
};
#[cfg(feature = "testonly")]
use crate::runtime::{
    algebra::{gf2_128::Gf2_128Field, p256::P256Field},
    v2::proto::composed::BodySizes,
};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::{
    core::algebra::SerializableField,
    mdoc::proto::adapter::QUOTIENT_BITS,
    runtime::{
        algebra::RuntimeField,
        v2::{foreign::word::MaskedWord, proto::composed::ComposedProof},
    },
};
/// A masked link quotient as it appears in the proof.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) type MaskedQuotient = MaskedWord<{ QUOTIENT_BITS }>;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdocProofGeometry {
    pub body: ComposedGeometry,
}
/// The hash circuit hosts the signature circuit's shared values; the body's
/// adapter message is the two masked quotients.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(crate) struct MdocProof<F1: SerializableField, F2: SerializableField> {
    pub(crate) body: ComposedProof<F1, F2, [MaskedQuotient; 2]>,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl<F1: RuntimeField<2> + SerializableField, F2: RuntimeField<4> + SerializableField>
    MdocProof<F1, F2>
{
    /// The one version magic, outermost (proto I1).
    pub(crate) const MAGIC: [u8; 4] = *b"MDA7";
    /// The complete proof: `MAGIC`, the body, sealed with `transcript`
    /// (transcript I10). Only the mdoc prover, which owns the session, seals
    /// one.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn write(
        &self,
        g: &ComposedGeometry,
        f1: &F1,
        f2: &F2,
        transcript: Transcript,
    ) -> Result<EncodedProof, String> {
        let mut out = Vec::new();
        out.extend_from_slice(&Self::MAGIC);
        self.body.write_to_buf(&mut out, g, f1, f2)?;
        Ok(transcript.append_final_seal(out))
    }
    /// Parse one complete MDA7 proof against the absorbed geometry (proto
    /// I2). Its length is checked before anything is decoded (proto I3), and
    /// it must end exactly with its final seal.
    #[cfg(any(test, feature = "verifier"))]
    pub(crate) fn read<'a>(
        bytes: &'a [u8],
        g: &Bound<'_, ComposedGeometry>,
        f1: &F1,
        f2: &F2,
    ) -> Result<Unverified<'a, Self>, String> {
        let geometry = g.part();
        let fixed = ComposedProof::<F1, F2, [MaskedQuotient; 2]>::fixed_len(geometry, f1, f2)
            .ok_or("mdoc proof geometry")?;
        let (t, n) = (geometry.config().t, geometry.config().n);
        let encoded =
            checked_body(bytes, Self::MAGIC.len(), fixed, t, n).map_err(|e| e.to_string())?;
        if bytes[..4] != Self::MAGIC {
            return Err("mdoc adapter proof version".into());
        }
        let body = ComposedProof::read(encoded, geometry, f1, f2)?;
        let mut seal = &bytes[bytes.len() - SEAL_BYTES..];
        Unverified::decoded(Self { body }, bytes, &mut seal).map_err(|e| e.to_string())
    }
}

/// The sizes of the body parts of `bytes`, a complete proof of `geometry`,
/// for the benchmarks' size report: the host is the hash circuit, the split
/// participant the signature circuit, and the adapter message the two masked
/// quotients. It parses the proof on a bare session and checks no seal.
#[cfg(feature = "testonly")]
pub fn proof_sizes(bytes: &[u8], geometry: &MdocProofGeometry) -> Result<BodySizes, String> {
    let (binary, prime) = (Gf2_128Field::new(), P256Field::new());
    let mut session = Transcript::for_test(b"sizes");
    let decoded = MdocProof::read(bytes, &session.bound(&geometry.body), &binary, &prime)?;
    decoded.body.sizes(&geometry.body, &binary, &prime)
}
