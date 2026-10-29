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

pub mod algsimp;
mod arena;
pub mod assertion;
#[cfg(feature = "experimental")]
mod boolean_witness;
pub mod copy;
pub mod cse;
pub mod ir;
pub mod ir_to_quad;
pub mod logic_impl;
pub mod node;
pub mod quad;
pub mod segment;
mod stats;
pub mod v1;
pub mod v2;
mod v2_segment;

pub use debug::{
    AssertionSymbol, CircuitDebugSymbols, CompiledAssertionStatus, CompiledEvalAssertions,
    EvaluatedCompiledAssertion, WireRef,
};
pub use ir::AssertionItem;
pub use logic_impl::{CompilerAssertions, CompilerLogic};
pub use segment::{segment_circuit, segment_layer};
pub use stats::dump_stats;
pub use v1::compile as compile_v1;
pub use v2::compile as compile_v2;
pub use v2_segment::segment_circuit_v2;

pub use crate::compile::proto::debug;

#[cfg(test)]
test_compilers!("../tests/all/mod.rs");

#[cfg(test)]
#[path = "../tests/backends.rs"]
mod backend_tests;

pub use v2::compile_with_classes as compile_v2_with_classes;

pub use crate::core::proto::fixed::CoefficientClasses;
