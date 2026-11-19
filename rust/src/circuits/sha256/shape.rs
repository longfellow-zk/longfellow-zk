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

//! The witness layout of one SHA-256 block: one 32-bit word per entry, in
//! declaration order. The circuit holds a shape of `V32` wires, the native
//! witness a shape of `u32`; `from_fn` allocates the inputs, `for_each`
//! encodes them in the same order, and `map` converts one into the other.
//!
//! `constants` holds the round constants and the initial chaining value, which
//! the circuit and the native witness both compute with.
pub mod constants;

/// The block's message words and the chaining value it starts from.
#[derive(Clone, Debug)]
pub struct Given<T> {
    pub input_block: [T; 16],
    pub h0: [T; 8],
}

/// The expanded message words 16..64, the new `e` and `a` of each round, and
/// the chaining value the block produces.
#[derive(Clone, Debug)]
pub struct Derived<T> {
    pub outw: [T; 48],
    pub oute: [T; 64],
    pub outa: [T; 64],
    pub h1: [T; 8],
}

impl<T> Given<T> {
    pub fn from_fn(mut next: impl FnMut() -> T) -> Self {
        let input_block = std::array::from_fn(|_| next());
        let h0 = std::array::from_fn(|_| next());
        Self { input_block, h0 }
    }

    pub fn for_each(&self, f: impl FnMut(&T)) {
        self.input_block.iter().chain(&self.h0).for_each(f);
    }

    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> Given<U> {
        Given {
            input_block: std::array::from_fn(|i| f(&self.input_block[i])),
            h0: std::array::from_fn(|i| f(&self.h0[i])),
        }
    }
}

impl<T> Derived<T> {
    pub fn from_fn(mut next: impl FnMut() -> T) -> Self {
        let outw = std::array::from_fn(|_| next());
        let oute = std::array::from_fn(|_| next());
        let outa = std::array::from_fn(|_| next());
        let h1 = std::array::from_fn(|_| next());
        Self {
            outw,
            oute,
            outa,
            h1,
        }
    }

    pub fn for_each(&self, f: impl FnMut(&T)) {
        self.outw
            .iter()
            .chain(&self.oute)
            .chain(&self.outa)
            .chain(&self.h1)
            .for_each(f);
    }

    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> Derived<U> {
        Derived {
            outw: std::array::from_fn(|i| f(&self.outw[i])),
            oute: std::array::from_fn(|i| f(&self.oute[i])),
            outa: std::array::from_fn(|i| f(&self.outa[i])),
            h1: std::array::from_fn(|i| f(&self.h1[i])),
        }
    }
}

impl<T: Copy> Derived<T> {
    /// The order of Longfellow v1's witness, which interleaves each round's
    /// `e` and `a`. v1 is frozen, so this order must not change.
    pub fn legacy_elements(&self) -> impl Iterator<Item = T> + '_ {
        self.outw
            .iter()
            .copied()
            .chain(self.oute.iter().zip(&self.outa).flat_map(|(&e, &a)| [e, a]))
            .chain(self.h1.iter().copied())
    }
}
