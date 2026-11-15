// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Shared layout of the selected SHAKE256 witnesses.

pub(crate) const SHAKE256_RATE: usize = 136;
pub(crate) const KECCAK_ROUNDS: usize = 24;
// State snapshots after the first round, then after each group of four rounds.
pub(crate) const STATE_ROUNDS: [usize; 7] = [0, 3, 7, 11, 15, 19, 23];

/// Explicit experimental choices for characteristic-two Keccak circuits.
/// The measured default commits every sixth round, materializes theta's column
/// parities, expands chi as `a + c + b*c`, and packs Boolean checkpoint equalities.
/// These choices change circuit structure without changing the Keccak relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryKeccak {
    /// Defer Keccak permutations to the authenticated packed SIMD frontend.
    pub external_permutations: bool,
    /// Rounds between committed states; a positive divisor of 24. Zero selects
    /// the historical irregular schedule after rounds 0, 3, 7, 11, 15, 19, 23.
    pub rounds_per_slice: usize,
    /// 0: inline theta; 1: materialize C; 2: materialize D; 3: both.
    pub theta_mode: u8,
    /// Materialize chi's result before the following round's linear operations.
    pub materialize_chi: bool,
    /// Use `a + c + b*c` for chi instead of `a + (1+b)*c`.
    pub expanded_chi: bool,
    /// Pack up to 128 checkpoint bit equalities into a basis-weighted field
    /// equality, retaining explicit Boolean constraints on committed bits.
    /// False selects coordinate equalities, which enforce Booleanity inductively.
    pub packed_checkpoints: bool,
}

impl Default for BinaryKeccak {
    fn default() -> Self {
        Self {
            external_permutations: false,
            rounds_per_slice: 6,
            theta_mode: 1,
            materialize_chi: false,
            expanded_chi: true,
            packed_checkpoints: true,
        }
    }
}

impl BinaryKeccak {
    /// Historical snapshot schedule, retained by odd-characteristic SHAKE.
    pub const fn legacy() -> Self {
        Self {
            external_permutations: false,
            rounds_per_slice: 0,
            theta_mode: 0,
            materialize_chi: false,
            expanded_chi: false,
            packed_checkpoints: true,
        }
    }
    pub fn validate(self) {
        assert!(
            self.rounds_per_slice <= KECCAK_ROUNDS
                && (self.rounds_per_slice == 0
                    || KECCAK_ROUNDS.is_multiple_of(self.rounds_per_slice)),
            "Keccak slice must be zero or a positive divisor of 24"
        );
        assert!(
            self.theta_mode <= 3,
            "Keccak theta mode must be 0 through 3"
        );
    }

    pub fn checkpoint(self, round: usize) -> bool {
        if self.rounds_per_slice == 0 {
            STATE_ROUNDS.contains(&round)
        } else {
            (round + 1).is_multiple_of(self.rounds_per_slice)
        }
    }

    pub fn checkpoint_count(self) -> usize {
        if self.external_permutations {
            return 2;
        }
        KECCAK_ROUNDS
            .checked_div(self.rounds_per_slice)
            .unwrap_or(STATE_ROUNDS.len())
    }

    pub fn is_legacy(self) -> bool {
        self == Self::legacy()
    }

    pub fn label(self) -> String {
        let mut label = format!(
            "s{}-t{}-c{}-e{}-p{}",
            self.rounds_per_slice,
            self.theta_mode,
            u8::from(self.materialize_chi),
            u8::from(self.expanded_chi),
            u8::from(self.packed_checkpoints)
        );
        if self.external_permutations {
            label.push_str("-simd");
        }
        label
    }
}

/// The proof frontend used for the Keccak permutations of a SHAKE sponge.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum KeccakBackend {
    #[default]
    Scalar,
    Permutations,
    Rounds,
}
impl KeccakBackend {
    pub fn label(self) -> &'static str {
        match self {
            Self::Scalar => "scalar",
            Self::Permutations => "permutations",
            Self::Rounds => "rounds",
        }
    }
}
