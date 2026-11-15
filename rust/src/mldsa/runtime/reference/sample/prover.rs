// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
impl ConcreteSampleInBallWitness {
    pub(crate) fn binary_bits_with_keccak(
        &self,
        keccak: BinaryKeccak,
    ) -> impl Iterator<Item = bool> + '_ {
        self.prefix_bits()
            .chain(self.shake.bits_with_keccak(keccak))
            .chain(self.suffix_bits())
    }
}
