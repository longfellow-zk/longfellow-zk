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
use crate::core::algebra::SerializableField;

pub(crate) mod arch;
pub mod blas;
pub mod fft;
mod field;
pub mod fp2;
pub mod fp_generic;
pub mod gf2_128;
pub mod lch14;
pub mod limb;
mod nat;
pub mod p256;
pub mod packing;
pub(in crate::runtime::algebra) mod permutations;
mod poly;
pub mod q256;
pub mod range_interpolation;
pub mod rfft;
pub mod secp256r1;

#[cfg(test)]
pub(crate) use field::batch_inverse;
pub use field::{
    RuntimeBinaryField, RuntimeField, RuntimeSerializableField, SupportsFFT,
    SupportsQuadraticExtension, SupportsSampling,
};
pub use nat::RuntimeNat;
pub use poly::{InterpolationField, LagrangeBasis, Poly};

/// Stable trait alias bundling requirements for zero-knowledge proving.
pub trait ZkField: InterpolationField + SerializableField + SupportsSampling {}
impl<F> ZkField for F where F: InterpolationField + SerializableField + SupportsSampling {}

#[cfg(test)]
mod tests;
