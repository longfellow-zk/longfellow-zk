// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Application composition of the native claim, binary trees and shared opening.
mod native;
pub(super) use native::SharedParticipant;
mod binary;
pub(super) use binary::BinaryParticipant;

#[cfg(test)]
#[path = "../../../tests/v2_adapter.rs"]
mod tests;
