// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Bind authenticated mdoc field locations to the containing CBOR maps.
cfg_compiler! {
    mod circuit;
    pub use circuit::{assert_structure, AttributeInput, AttributeWitness, Input, Witness};
}
cfg_testonly! {
    mod evaluate;
}
#[cfg(test)]
mod tests;
