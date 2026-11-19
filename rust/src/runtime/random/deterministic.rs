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

use crate::runtime::random::{PrivateRandom, RandomEngine, Sealed};

/// A seeded generator for reproducible tests, built only with `testonly`. Its
/// coins are predictable, so a v2 proof made with it reveals its witness.
#[derive(Clone, Debug)]
pub struct DeterministicRng {
    pub state: u64,
}

impl RandomEngine for DeterministicRng {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut buf = vec![0u8; len];
        self.fill(&mut buf);
        buf
    }
    fn fill(&mut self, out: &mut [u8]) {
        for b in out {
            self.state = self
                .state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            *b = (self.state >> 56) as u8;
        }
    }
}

impl DeterministicRng {
    #[must_use]
    pub fn new(state: u64) -> Self {
        Self { state }
    }
}

impl Sealed for DeterministicRng {}
impl PrivateRandom for DeterministicRng {}
