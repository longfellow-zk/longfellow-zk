// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Offline coefficient policy selection shared by the ablation benchmarks.
pub fn from_env<T: Default>(classes: impl FnOnce(bool, bool) -> T) -> T {
    match std::env::var("CIRCUIT_COEFFICIENT_CLASSES").ok().as_deref() {
        Some("zero") => classes(false, false),
        Some("one") => classes(true, false),
        Some("minus") => classes(false, true),
        Some("all") => classes(true, true),
        None => T::default(),
        Some(value) => panic!(
            "unknown CIRCUIT_COEFFICIENT_CLASSES={value:?}; expected zero, one, minus, or all"
        ),
    }
}
