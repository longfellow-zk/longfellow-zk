// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compile-time ML-DSA relations. Native witnesses live under `runtime`.
mod binary;
pub(crate) mod hidden;
mod polynomial;
mod sample;
mod shake;
mod shared;
pub(crate) use binary::{allocate_private, signature_assertions};
