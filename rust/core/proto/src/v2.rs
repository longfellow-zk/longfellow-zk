// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 circuits: quadratic, linear, and constant streams.
//!
//! `k` indexes the circuit's coefficient table. Coordinate deltas wrap modulo
//! 2^32; coefficient indices are absolute, with no reserved entries.
//! Quadratic and linear records whose coefficient is zero are assertions.
use super::SerializableField;

pub mod archive;
mod directory;
pub(crate) mod encoding;
pub mod limits;
pub mod reader;
mod uleb;
pub mod writer;
pub use reader::CircuitReader;
pub use writer::CircuitWriter;
#[cfg(test)]
#[path = "../tests/v2_fixtures.rs"]
mod fixtures;
pub use encoding::compute_id;
#[cfg(test)]
pub(crate) use fixtures::{quadratic_fixture, quadratic_layer_fixture};

mod circuit;
pub use circuit::{Circuit, CircuitParts, RawCircuit, RawCircuitBuilder};

mod layer;
pub use layer::{classify_constants, CoefficientClass, Constant, Layer, Linear, Quadratic};

mod stream;
pub use stream::{Segments, Stream};
