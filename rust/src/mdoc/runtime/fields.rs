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

//! Field requirements of the v1 mdoc runtime's native witness derivation.

use crate::{
    core::algebra::{
        BareField, HasLookupPoints, Nat, SupportsNatConversions, SupportsU64Conversions,
    },
    runtime::algebra::RuntimeField,
};

/// Bundles all runtime derived value derivation and evaluation requirements for `MdocHash`.
pub(crate) trait MdocHashRuntimeField:
    Sized
    + RuntimeField
    + crate::core::algebra::SerializableField
    + HasLookupPoints
    + crate::core::algebra::SupportsU128Conversions
{
}

impl<F> MdocHashRuntimeField for F where F: Sized
        + RuntimeField
        + crate::core::algebra::SerializableField
        + HasLookupPoints
        + crate::core::algebra::SupportsU128Conversions
{
}

/// Bundles all runtime derived value derivation requirements for signature field arithmetic.
pub(crate) trait MdocSigRuntimeField:
    Sized
    + BareField
    + RuntimeField
    + SupportsNatConversions<4>
    + SupportsU64Conversions
    + HasLookupPoints
where <Self as SupportsNatConversions<4>>::N: Nat<4>
{
}

impl<F> MdocSigRuntimeField for F
where
    F: Sized
        + BareField
        + RuntimeField
        + SupportsNatConversions<4>
        + SupportsU64Conversions
        + HasLookupPoints,
    <F as SupportsNatConversions<4>>::N: Nat<4>,
{
}
