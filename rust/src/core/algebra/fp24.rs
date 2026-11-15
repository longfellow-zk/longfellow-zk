// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Agreed constants for the ML-DSA prime and its sextic extension.
//! Arithmetic belongs separately to compile::algebra and runtime::algebra.
pub const Q: u32 = 8_380_417;
pub const BETA: u32 = 7;
pub const BASE_SERIALIZED_SIZE: usize = 3;
pub const EXTENSION_DEGREE: usize = 6;
pub const SERIALIZED_SIZE: usize = BASE_SERIALIZED_SIZE * EXTENSION_DEGREE;

#[cfg(test)]
mod tests;
