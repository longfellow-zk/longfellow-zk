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

pub mod circuit;

pub use crate::mdoc::proto::mso_attribute::constants;
pub use circuit::{
    AttrIndex, AttrSlice, AttributeVerifier, Derived, DisclosedAttribute, FieldLocator, Given,
    Slice,
};

cfg_testonly! {
    pub mod allocate;
    pub mod concrete;
    pub mod evaluate;

    pub use self::{
        allocate::{allocate_derived, allocate_given},
        concrete::{derived, ConcreteDerived, ConcreteGiven},
        evaluate::{evaluate_derived, evaluate_given},
    };
}

