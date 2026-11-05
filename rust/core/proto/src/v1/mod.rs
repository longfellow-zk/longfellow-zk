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

//! Frozen v1 circuit representation and LFC1/LFC2 codecs.

pub mod cache;
mod circuit;
mod layer;
pub mod reader;
mod term;
pub mod writer;

pub use circuit::{compute_id, Circuit, RawCircuit};
pub use layer::{compare_term, Layer, TermDelta};
pub use reader::CircuitReader;
pub use term::{canonical_term, Term};
pub use writer::CircuitWriter;

pub use crate::core::proto::CircuitGeometry;

pub const BYTES_PER_SIZE_T: usize = 3;
