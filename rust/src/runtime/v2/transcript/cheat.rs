// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test-only cheating prover. While `cheating` runs a closure, the v2 prover
//! on that thread skips its own checks of the witness and of the claims it
//! derives (circuit assertions and outputs, the sumcheck terminal product,
//! the packing trace, the P-256 adapter's quotients), so that a false
//! statement reaches the verifier, whose checks the soundness tests then
//! exercise. Production builds compile none of it, and outside `cheating`
//! the prover behaves as in production.

thread_local! {
    static CHEATING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether the prover's self-checks are off on this thread.
pub(crate) fn active() -> bool {
    CHEATING.with(std::cell::Cell::get)
}

/// Run `f` with the prover's self-checks off on this thread.
pub(crate) fn cheating<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            CHEATING.with(|c| c.set(self.0));
        }
    }
    let _restore = Restore(CHEATING.with(|c| c.replace(true)));
    f()
}
