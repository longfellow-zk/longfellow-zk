// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! 128-lane Boolean SHA-256 circuit and its separately derived packed witness.
mod shape;
pub use shape::INPUT_BITS;
cfg_compiler! {mod circuit;mod logic;mod flat;pub use flat::{compile,Affine,FlatCircuit,Policy};}
cfg_prover! {mod concrete;pub use concrete::pack_instances;}
#[cfg(test)]
mod tests;
