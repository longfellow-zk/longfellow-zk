// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Application composition of the prime claim, binary trees and shared opening.
mod masked_prime;
mod prime;
pub(super) mod transcript;
pub(super) use prime::SharedParticipant;
mod binary;
pub(super) use binary::BinaryParticipant;

#[cfg(test)]
#[path = "../../../tests/v2_adapter.rs"]
mod tests;
