// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::Transcript;
/// Complete-verification evidence, never returned by intermediate verifiers.
#[derive(Debug, PartialEq, Eq)]
pub struct VerifiedProof {
    _private: (),
    #[cfg(test)]
    trace: super::trace::Trace,
}
#[cfg(test)]
impl VerifiedProof {
    pub(crate) fn round_count_for_test(&self) -> u64 {
        self.trace.boundaries()
    }
    pub(crate) fn trace_for_test(&self) -> &super::trace::Trace {
        &self.trace
    }
}

impl Transcript {
    #[cfg(any(test, feature = "verifier"))]
    pub(crate) fn verify_final_seal(mut self, bytes: &[u8]) -> Result<VerifiedProof, &'static str> {
        let n = bytes
            .len()
            .checked_sub(super::SEAL_BYTES)
            .ok_or("missing final seal")?;
        if self.compute_final_seal(&bytes[..n]) != bytes[n..] {
            return Err("final seal mismatch");
        }
        Ok(VerifiedProof {
            _private: (),
            #[cfg(test)]
            trace: self.trace,
        })
    }
}
/// Parsed, immutable protocol data. Decoding alone grants no verification token.
#[derive(Debug)]
pub struct Unverified<'a, P> {
    body: P,
    _encoded: &'a [u8],
}
impl<P> std::ops::Deref for Unverified<'_, P> {
    type Target = P;
    fn deref(&self) -> &P {
        &self.body
    }
}
impl<'a, P> Unverified<'a, P> {
    /// `input` is the whole proof, which must end in exactly one seal block
    /// after the `remaining` bytes the body reader left.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn decoded(
        body: P,
        input: &'a [u8],
        remaining: &mut &'a [u8],
    ) -> Result<Self, std::io::Error> {
        if remaining.len() != super::SEAL_BYTES {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "complete v2 proof must end in one final seal",
            ));
        }
        *remaining = &[];
        Ok(Self {
            body,
            _encoded: input,
        })
    }
    #[cfg(any(test, feature = "verifier"))]
    pub(crate) fn checked(self, transcript: Transcript) -> Result<VerifiedProof, &'static str> {
        transcript.verify_final_seal(self._encoded)
    }
}
