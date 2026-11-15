// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! CBOR framing over a fixed-capacity buffer and a witnessed input range.
//! Supports definite strings, arrays, maps, tags, integers and simple values.
//! Float values, indefinite encodings, UTF-8 and key uniqueness are outside this layer.
cfg_compiler! {
    mod circuit;
    pub use circuit::{CborLexer, Lexed, Witness};
    pub(in crate::mdoc::circuits) mod counter;
}
#[cfg(test)]
mod tests;
