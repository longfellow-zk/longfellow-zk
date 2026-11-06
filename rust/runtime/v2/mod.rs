// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The selected-witness protocol, using explicit transcript rounds, packing,
//! layered sumcheck and one joint Polygero commitment.

#[path = "dual-packing/src/lib.rs"]
pub mod dual_packing;
#[path = "polygero/src/lib.rs"]
pub mod polygero;
#[path = "proto/src/lib.rs"]
pub mod proto;
#[path = "sumcheck/src/lib.rs"]
pub mod sumcheck;
#[path = "transcript/src/lib.rs"]
pub mod transcript;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[path = "witness-selection/src/lib.rs"]
pub mod witness_selection;
#[path = "zk/src/lib.rs"]
pub mod zk;
