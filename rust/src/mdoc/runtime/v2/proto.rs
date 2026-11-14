// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The mdoc envelope: version `MDA7`, a composed proof body, the final seal.
use crate::{
    core::proto::SerializableField,
    runtime::{
        algebra::RuntimeField,
        v2::proto::composed::{ComposedGeometry, ComposedProof},
    },
};
/// A masked link quotient as it appears in the proof.
pub type MaskedQuotient = crate::runtime::v2::foreign::word::MaskedWord<
    { crate::mdoc::circuits::p256_adapter::QUOTIENT_BITS },
>;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdocProofGeometry {
    pub body: ComposedGeometry,
}
/// The hash circuit hosts the signature circuit's shared values; the body's
/// adapter message is the two masked quotients.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdocProof<F1: SerializableField, F2: SerializableField> {
    pub body: ComposedProof<2, F1, 4, F2, [MaskedQuotient; 2]>,
}
impl<F1: RuntimeField<2> + SerializableField, F2: RuntimeField<4> + SerializableField>
    MdocProof<F1, F2>
{
    pub fn write(
        &self,
        g: &MdocProofGeometry,
        f1: &F1,
        f2: &F2,
        transcript: crate::runtime::v2::transcript::Transcript,
    ) -> Result<crate::runtime::v2::transcript::EncodedProof, String> {
        let mut out = Vec::new();
        out.extend_from_slice(b"MDA7");
        self.body.write_to_buf(&mut out, &g.body, f1, f2)?;
        Ok(transcript.append_final_seal(out))
    }
    /// Parse one complete MDA7 proof, which must end exactly with its final seal.
    pub fn read<'a>(
        bytes: &'a [u8],
        g: &MdocProofGeometry,
        f1: &F1,
        f2: &F2,
    ) -> Result<crate::runtime::v2::transcript::Unverified<'a, Self>, String> {
        if bytes.get(..4) != Some(b"MDA7") {
            return Err("mdoc adapter proof version or size".into());
        }
        let mut remaining = &bytes[4..];
        let body = ComposedProof::read(&mut remaining, &g.body, f1, f2)?;
        // The proof must end exactly with its final seal; no trailing data is
        // returned to the caller.
        crate::runtime::v2::transcript::Unverified::decoded(Self { body }, bytes, &mut remaining)
            .map_err(|e| e.to_string())
    }
}
