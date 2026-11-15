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
pub mod cse;
pub(crate) mod graph;
pub mod ir;
mod logic_impl;
pub mod node;
mod scheduling;
mod segment;
mod stats;
mod v2;
mod v2_segment;

pub use arena::CompilerArena;
pub use logic_impl::{CompilerAssertions, CompilerLogic};
pub use stats::dump_stats;
pub use v2::{compile_v2, compile_v2_shared_inputs};
pub use v2_segment::segment_circuit_v2;

cfg_testonly! {
    mod v1;
    pub use v1::{compile_v1, segment_circuit_v1, segment_layer_v1};
}

#[cfg(test)]
pub(crate) mod tests;
