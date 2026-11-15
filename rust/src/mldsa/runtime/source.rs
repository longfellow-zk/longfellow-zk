// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Authenticated packed sources for the ordinary scalar SHAKE sponge circuit.
use crate::{
    mldsa::proto::KeccakBackend,
    runtime::v2::simd_sumcheck::{Program, SharedShake, SharedShakeRounds},
};
pub enum KeccakSource {
    Permutations(SharedShake),
    Rounds(SharedShakeRounds),
}
impl KeccakSource {
    pub fn new(
        backend: KeccakBackend,
        private: usize,
        links: Vec<(Vec<usize>, Vec<usize>)>,
    ) -> Result<Self, String> {
        match backend {
            KeccakBackend::Scalar => Err("scalar Keccak has no packed source".into()),
            KeccakBackend::Permutations => SharedShake::new(private, links).map(Self::Permutations),
            KeccakBackend::Rounds => SharedShakeRounds::new(private, links).map(Self::Rounds),
        }
    }
    pub fn program(&self) -> &Program {
        match self {
            Self::Permutations(s) => &s.program,
            Self::Rounds(s) => &s.program,
        }
    }
    pub fn placements(&self) -> &[(usize, u8)] {
        match self {
            Self::Permutations(s) => s.placements(),
            Self::Rounds(s) => s.placements(),
        }
    }
    pub fn metadata_bytes(&self) -> Vec<u8> {
        match self {
            Self::Permutations(s) => s.metadata_bytes(),
            Self::Rounds(s) => s.metadata_bytes(),
        }
    }
}

cfg_prover! { mod prover; }
