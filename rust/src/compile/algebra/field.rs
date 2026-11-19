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

use crate::core::algebra::{AlgebraicField, Comparable, HasLookupPoints, SerializableField};

/// Trait for fields used at circuit compile-time. Inherits from
/// [`crate::core::algebra::AlgebraicField`] to define its associated
/// [`crate::core::algebra::BareField::E`] type and algebraic operations.
pub trait CompileField: AlgebraicField + SerializableField + Comparable + HasLookupPoints {
    /// Returns the i-th basis vector allowing binary combinations with
    /// coefficients {0,1} to represent any field element.
    fn pseudo_basis(&self, i: usize) -> Self::E;

    /// Returns the dimension (number of independent basis vectors) of the field.
    fn pseudo_dimension(&self) -> usize;

    /// Returns the i-th basis vector of the field without checking
    /// dimension boundaries.
    fn pseudo_basis_unsafe(&self, i: usize) -> Self::E;

    fn pseudo_dimension_of_multiplicative_group(&self) -> usize;
}

pub trait CompilePrimeField: CompileField {}

pub trait CompileBinaryField: CompileField {
    fn generator(&self) -> Self::E;
}
