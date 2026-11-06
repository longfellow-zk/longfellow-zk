// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::Transcript;
/// Complete-verification evidence, never returned by intermediate verifiers.
#[derive(Debug, PartialEq, Eq)]
pub struct VerifiedProof {
    _private: (),
}

impl Transcript {
    #[cfg(any(test, feature = "verifier"))]
    pub(crate) fn verify_final_seal(self, bytes: &[u8]) -> Result<VerifiedProof, &'static str> {
        let n = bytes.len().checked_sub(32).ok_or("missing final seal")?;
        if self.compute_final_seal(&bytes[..n]) != bytes[n..] {
            return Err("final seal mismatch");
        }
        Ok(VerifiedProof { _private: () })
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
    pub(crate) fn decoded(
        body: P,
        input: &'a [u8],
        remaining: &mut &'a [u8],
    ) -> Result<Self, std::io::Error> {
        if remaining.len() != 32 {
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
