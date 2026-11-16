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

mod circuit;
mod shape;

pub use circuit::{AttrGiven, Given, HashBytes, MdocHash};
pub use shape::{AttrDerived, Derived};

cfg_compiler! {
    mod allocate;
    pub use allocate::allocate;
}

cfg_testonly! {
    mod concrete;
    mod evaluate;

    pub use self::{
        concrete::{
            derived, given, hash_input_of_parsed_mdoc, AttrInput, ConcreteAttrGiven,
            ConcreteGiven, ConcreteHashBytes, HashInput,
        },
        evaluate::{evaluate_derived, evaluate_given},
    };
}
