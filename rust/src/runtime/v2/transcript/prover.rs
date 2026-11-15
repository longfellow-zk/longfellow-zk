// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::Transcript;
/// Bytes emitted only after complete-proof encoding has appended its final seal.
pub struct EncodedProof {
    bytes: Vec<u8>,
    #[cfg(test)]
    trace: super::trace::Trace,
}
impl EncodedProof {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
    #[cfg(test)]
    pub(crate) fn round_count_for_test(&self) -> u64 {
        self.trace.boundaries()
    }
    #[cfg(test)]
    pub(crate) fn trace_for_test(&self) -> &super::trace::Trace {
        &self.trace
    }
}

impl Transcript {
    /// Seal `body`, every proof byte before the seal block, and append the
    /// seal block (transcript I10).
    pub(crate) fn append_final_seal(mut self, body: Vec<u8>) -> EncodedProof {
        let final_seal = self.compute_final_seal(&body);
        let mut bytes = body;
        bytes.extend_from_slice(&final_seal);
        EncodedProof {
            bytes,
            #[cfg(test)]
            trace: self.trace,
        }
    }
}
