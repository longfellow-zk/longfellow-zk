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

mod field;
pub use field::{
    AlgebraicField, BareField, Comparable, ElementOf, FieldElement, FieldID, HasLookupPoints,
    NatOf, RegisteredField, SerializableField, SupportsNatConversions, SupportsU128Conversions,
    SupportsU64Conversions,
};

mod nat;
pub use nat::Nat;

pub mod ec;

pub mod encoding;

// A reference GF(2^128), the test oracle for both sides' fields.
#[cfg(test)]
mod gf2_128;
#[cfg(test)]
pub(crate) use gf2_128::Gf2_128Field;

mod proto;
pub use proto::{CANTOR_BASIS_U128, GF2_16_BASIS_V1, POLY_EVALUATION_POINTS};

#[cfg(test)]
mod tests;
