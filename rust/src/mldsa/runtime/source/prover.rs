// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::KeccakSource;
use crate::runtime::algebra::gf2_128::Gf2_128;
impl KeccakSource {
    pub(crate) fn witness(&self, private: &[bool]) -> Result<Vec<Gf2_128>, String> {
        match self {
            Self::Permutations(s) => s.witness(private),
            Self::Rounds(s) => s.witness(private),
        }
    }
}
