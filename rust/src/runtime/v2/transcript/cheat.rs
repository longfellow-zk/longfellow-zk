// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Test-only cheating prover. While `cheating` runs a closure, the v2 prover
//! on that thread skips its own checks of the witness and of the claims it
//! derives (circuit assertions and outputs, the sumcheck terminal product,
//! the packing trace, the P-256 adapter's quotients), so that a false
//! statement reaches the verifier, whose checks the soundness tests then
//! exercise. `cheating_from_host_bits` also makes the composed prover take
//! the foreign values of its split message and adapter from the host's
//! committed bits rather than from the split frontend's own values.
//! Production builds compile none of it, and outside these closures the
//! prover behaves as in production.
use std::cell::Cell;

thread_local! {
    static CHEATING: Cell<bool> = const { Cell::new(false) };
    static FROM_HOST_BITS: Cell<bool> = const { Cell::new(false) };
}

/// Whether the prover's self-checks are off on this thread.
pub(crate) fn active() -> bool {
    CHEATING.with(Cell::get)
}

/// Whether the composed prover on this thread takes its foreign values from
/// the host's bits.
pub(crate) fn from_host_bits() -> bool {
    FROM_HOST_BITS.with(Cell::get)
}

/// Set `flag` to true while `f` runs, then restore it, even if `f` panics.
fn with<T>(flag: &'static std::thread::LocalKey<Cell<bool>>, f: impl FnOnce() -> T) -> T {
    struct Restore(&'static std::thread::LocalKey<Cell<bool>>, bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            self.0.with(|c| c.set(self.1));
        }
    }
    let _restore = Restore(flag, flag.with(|c| c.replace(true)));
    f()
}

/// Run `f` with the prover's self-checks off on this thread.
pub(crate) fn cheating<T>(f: impl FnOnce() -> T) -> T {
    with(&CHEATING, f)
}

/// Run `f` with the prover's self-checks off and the composed prover's
/// foreign values taken from the host's bits.
pub(crate) fn cheating_from_host_bits<T>(f: impl FnOnce() -> T) -> T {
    with(&FROM_HOST_BITS, || cheating(f))
}
