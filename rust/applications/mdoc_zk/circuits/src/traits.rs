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

/// Bundles all runtime derived value derivation and evaluation requirements for `MdocHash`.
pub trait MdocHashRuntimeField:
    Sized
    + crate::runtime::algebra::field::RuntimeField<2>
    + crate::core::algebra::SerializableField
    + crate::core::algebra::HasLookupPoints
    + crate::core::algebra::SupportsU128Conversions
{
}

impl<F> MdocHashRuntimeField for F where F: Sized
        + crate::runtime::algebra::field::RuntimeField<2>
        + crate::core::algebra::SerializableField
        + crate::core::algebra::HasLookupPoints
        + crate::core::algebra::SupportsU128Conversions
{
}

/// Bundles all runtime derived value derivation requirements for signature field arithmetic.
pub trait MdocSigRuntimeField:
    Sized
    + crate::core::algebra::BareField
    + crate::runtime::algebra::field::RuntimeField<4>
    + crate::core::algebra::SupportsNatConversions<4>
    + crate::core::algebra::SupportsU64Conversions
    + crate::core::algebra::HasLookupPoints
where <Self as crate::core::algebra::SupportsNatConversions<4>>::N: crate::core::algebra::Nat<4>
{
}

impl<F> MdocSigRuntimeField for F
where
    F: Sized
        + crate::core::algebra::BareField
        + crate::runtime::algebra::field::RuntimeField<4>
        + crate::core::algebra::SupportsNatConversions<4>
        + crate::core::algebra::SupportsU64Conversions
        + crate::core::algebra::HasLookupPoints,
    <F as crate::core::algebra::SupportsNatConversions<4>>::N: crate::core::algebra::Nat<4>,
{
}

cfg_compiler! {
    use crate::compile::algebra::field::CompileField;

    /// Bundles all compile-time circuit generation requirements for `MdocHash`.
    pub trait MdocHashCompileField:
        Sized + CompileField + crate::circuits::analog_adder::FieldWrappingSum + crate::core::algebra::SerializableField
    {
    }

    impl<F> MdocHashCompileField for F where F: Sized
            + CompileField
            + crate::circuits::analog_adder::FieldWrappingSum
            + crate::core::algebra::SerializableField
    {
    }

}
