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

//! Shared field identifiers and circuit geometry.

pub type DigestBytes = [u8; 32];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldID {
    None = 0,
    P256 = 1,
    P384 = 2,
    P521 = 3,
    Gf2_128 = 4,
    Gf2_16 = 5,
    Fp128 = 6,
    Fp64 = 7,
    Goldi = 8,
    Fp64_2 = 9,
    Secp = 10,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CircuitGeometry {
    pub ninput: usize,
    pub npublic_input: usize,
    pub noutput: usize,
    pub nwires: usize,
    pub nterms: usize,
    pub nlayers: usize,
    pub nassertions: usize,
}
