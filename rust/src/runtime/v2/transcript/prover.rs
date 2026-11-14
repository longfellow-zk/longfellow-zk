// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::Transcript;
/// Bytes emitted only after complete-proof encoding has appended its final seal.
pub struct EncodedProof {
    bytes: Vec<u8>,
    #[cfg(test)]
    rounds: u64,
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
        self.rounds
    }
}

impl Transcript {
    pub(crate) fn append_final_seal(self, body: Vec<u8>) -> EncodedProof {
        #[cfg(test)]
        let rounds = self.round_count_for_test();
        let final_seal = self.compute_final_seal(&body);
        let mut bytes = body;
        bytes.extend_from_slice(&final_seal);
        EncodedProof {
            bytes,
            #[cfg(test)]
            rounds,
        }
    }
}
