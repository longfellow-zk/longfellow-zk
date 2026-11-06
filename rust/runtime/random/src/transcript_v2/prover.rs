// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::Transcript;
/// Bytes emitted only after complete-proof encoding has appended its final seal.
pub struct EncodedProof(Vec<u8>);
impl EncodedProof {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
    pub fn into_bytes(self) -> Vec<u8> {
        self.0
    }
}

impl Transcript {
    pub(crate) fn append_final_seal(self, body: Vec<u8>) -> EncodedProof {
        let final_seal = self.compute_final_seal(&body);
        let mut bytes = body;
        bytes.extend_from_slice(&final_seal);
        EncodedProof(bytes)
    }
}
