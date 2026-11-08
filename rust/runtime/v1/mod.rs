// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The deployed protocol. Its transcript, codecs and compact rows are independent
//! of the v2 protocol; shared arithmetic and private randomness remain in runtime.

#[path = "ligero/src/lib.rs"]
pub mod ligero;
#[path = "merkle/src/lib.rs"]
pub mod merkle;
#[path = "proto/src/lib.rs"]
pub mod proto;
pub mod random;
#[path = "subfield/src/lib.rs"]
pub mod subfield;
#[path = "sumcheck/src/lib.rs"]
pub mod sumcheck;
#[path = "transcript/src/lib.rs"]
pub mod transcript;
#[path = "zk/src/lib.rs"]
pub mod zk;
