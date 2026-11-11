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

use crate::runtime::algebra::SupportsSampling;

/// Trait defining operations for seedable/pseudorandom challenge engines.
pub trait RandomEngine {
    /// Generates raw pseudorandom bytes of the specified length.
    fn bytes(&mut self, len: usize) -> Vec<u8>;

    /// Generates a random field element.
    fn elt_field<F: SupportsSampling>(&mut self, f: &F) -> F::E {
        f.sample(|len| self.bytes(len))
    }

    /// Generates a slice of field elements with random values.
    fn elt_field_slice<F: SupportsSampling>(&mut self, len: usize, f: &F) -> Vec<F::E> {
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(self.elt_field(f));
        }
        v
    }

    /// Generates a random u128.
    fn u128(&mut self) -> u128 {
        let buf = self.bytes(16);
        u128::from_le_bytes(buf.try_into().unwrap())
    }
}

pub mod secure;
pub use secure::SecureRandomEngine;

cfg_testonly! {
    pub mod deterministic;
    pub use deterministic::DeterministicRng;
}
