// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Stack-free CBOR structure and direct map-key/value membership.
//! One global pending-slot rank trace and one threshold trace per selected map.
cfg_compiler! {
    mod circuit;
    pub use circuit::{CborParser, CheckedItem, CheckedMap, Entry, Parsed, RankWitness, Span, Witness};
}
#[cfg(test)]
mod tests;
