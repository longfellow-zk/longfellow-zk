#![deny(unreachable_pub, private_interfaces)]
// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared arithmetic and primitives, with independent protocol implementations.
//! Each item has one path: shared code under `algebra` and `random`, each
//! protocol under its own version.

#[path = "algebra/src/lib.rs"]
pub mod algebra;
#[path = "random/src/lib.rs"]
pub mod random;
#[cfg(feature = "v1")]
pub mod v1;
pub mod v2;
