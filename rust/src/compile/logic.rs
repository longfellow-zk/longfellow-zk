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

pub mod eval;
// `compile::logic::logic` mirrors the layout of the former `compile-logic` crate.
#[allow(clippy::module_inception)]
pub mod logic;
pub mod scope;

pub mod tracker {
    pub use crate::compile::logic::scope::AssertionScope as AssertionTracker;
}

pub use crate::compile::logic::{
    eval::EvalContext,
    logic::{Eltw, Logic, LogicIO, K_FIRST_WIRE_POSITION},
    scope::AssertionScope,
};

cfg_testonly! {
    pub mod concrete;
    pub use concrete::*;
}

#[cfg(test)]
mod tests;
