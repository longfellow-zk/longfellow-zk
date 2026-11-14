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

//! Field requirements of the mdoc circuits at compile time.

use crate::{
    circuits::analog_adder::FieldWrappingSum, compile::algebra::CompileField,
    core::algebra::SerializableField,
};

/// Bundles all compile-time circuit generation requirements for `MdocHash`.
pub trait MdocHashCompileField:
    Sized + CompileField + FieldWrappingSum + SerializableField
{
}

impl<F> MdocHashCompileField for F where F: Sized + CompileField + FieldWrappingSum + SerializableField
{}
