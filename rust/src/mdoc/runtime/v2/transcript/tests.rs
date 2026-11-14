// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

/// The spec's combined archive hash must change every later challenge.
#[test]
fn statement_binds_combined_hash() {
    let hash = [7u8; 32];
    let mut other = hash;
    other[0] ^= 1;
    assert_ne!(
        new(b"session", &hash).bytes(32),
        new(b"session", &other).bytes(32),
        "combined hash is not bound"
    );
}

/// The public presentation bits must change every later challenge.
#[test]
fn statement_binds_public_inputs() {
    let with_public = |public: &[bool]| {
        let mut t = new(b"session", &[7; 32]);
        absorb_public_inputs(&mut t.borrow(), public);
        t.bytes(32)
    };
    assert_ne!(
        with_public(&[false, true]),
        with_public(&[true, true]),
        "public inputs are not bound"
    );
}
