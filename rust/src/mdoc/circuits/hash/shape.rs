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

//! The derived witness layout of the mdoc hash circuit: one message-hash
//! witness per disclosed attribute, in request order, then the MSO's. The
//! circuit holds a shape of `V32` wires, the native witness a shape of `u32`.
//!
//! The given inputs have no shape: their entries have many widths, and the
//! native given carries test-support data, so the circuit's `Given` and the
//! native `ConcreteGiven` stay separate. The allocator interleaves each
//! attribute's given and derived wires; the shape fixes only their contents.

use crate::circuits::sha256msg::Derived as MsgDerived;

/// One disclosed attribute's message-hash witness (two SHA-256 blocks).
#[derive(Clone, Debug)]
pub struct AttrDerived<T> {
    pub sha_derived: MsgDerived<T>,
}

#[derive(Clone, Debug)]
pub struct Derived<T> {
    pub attribute_derived: Vec<AttrDerived<T>>,
    pub sha_derived: MsgDerived<T>,
}

impl<T> Derived<T> {
    pub fn map<U>(&self, mut f: impl FnMut(&T) -> U) -> Derived<U> {
        Derived {
            attribute_derived: self
                .attribute_derived
                .iter()
                .map(|a| AttrDerived {
                    sha_derived: a.sha_derived.map(&mut f),
                })
                .collect(),
            sha_derived: self.sha_derived.map(&mut f),
        }
    }
}
