// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Trace-zero response. A degree-one extension has no messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackingProof<E> {
    Direct,
    TraceZero { u: Vec<E>, a: E },
}
