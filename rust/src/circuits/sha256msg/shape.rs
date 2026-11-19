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

//! The derived witness layout of a message hash: one SHA-256 block witness
//! per block the circuit can hash, in block order. The circuit holds a shape
//! of `V32` wires, the native witness a shape of `u32`.
//!
//! The given inputs have no shape: their entries have four widths (the
//! block count, the length, the preimage bytes and the digest), so the
//! circuit's `Given` and the native `ConcreteGiven` stay separate.

use crate::circuits::sha256::Derived as BlockDerived;

#[derive(Clone, Debug)]
pub struct Derived<T> {
    pub sha_derived: Vec<BlockDerived<T>>,
}

impl<T> Derived<T> {
    /// A shape of `nblocks` block witnesses.
    pub fn from_fn(nblocks: usize, mut next: impl FnMut() -> T) -> Self {
        Self {
            sha_derived: (0..nblocks)
                .map(|_| BlockDerived::from_fn(&mut next))
                .collect(),
        }
    }

    pub fn for_each(&self, mut f: impl FnMut(&T)) {
        for block in &self.sha_derived {
            block.for_each(&mut f);
        }
    }

    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> Derived<U> {
        Derived {
            sha_derived: self
                .sha_derived
                .iter()
                .map(|block| block.map(&mut f))
                .collect(),
        }
    }
}
