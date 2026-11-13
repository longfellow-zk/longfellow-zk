// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Named private-input positions of the mdoc v2 circuits, shared by the
//! circuit compiler, the witness encoders and the runtime link.
//!
//! Positions are relative to each circuit's public prefix. The signature
//! circuit stores its first private inputs, one input per bit, as bits of the
//! hash circuit's witness; `SHARED` pairs each such signature range with its
//! hash range. The compiler and the encoders check their allocation order
//! against these ranges, and the link reads them, so this table is the single
//! description of the shared positions.
use core::ops::Range;

use super::hash::constants::{K_HASH_INDEX_BITS, K_MSO_PREIMAGE_LEN};

const fn after(previous: Range<usize>, width: usize) -> Range<usize> {
    previous.end..previous.end + width
}

/// The hash circuit's leading private inputs, in allocation order.
pub mod hash {
    use super::{after, Range, K_HASH_INDEX_BITS, K_MSO_PREIMAGE_LEN};
    pub const ISSUER_DIGEST: Range<usize> = 0..256;
    pub const MSO_PREIMAGE: Range<usize> = after(ISSUER_DIGEST, 8 * K_MSO_PREIMAGE_LEN);
    pub const MSO_LEN: Range<usize> = after(MSO_PREIMAGE, K_HASH_INDEX_BITS);
    pub const NBLOCKS: Range<usize> = after(MSO_LEN, 8);
    pub const DEVICE_X: Range<usize> = after(NBLOCKS, 256);
    pub const DEVICE_Y: Range<usize> = after(DEVICE_X, 256);
}

/// The signature circuit's leading private inputs, in allocation order.
pub mod sig {
    use super::{after, Range};
    pub const ISSUER_DIGEST: Range<usize> = 0..256;
    pub const DEVICE_X: Range<usize> = after(ISSUER_DIGEST, 256);
    pub const DEVICE_Y: Range<usize> = after(DEVICE_X, 256);
}

/// Each value the signature circuit stores in the hash witness: its signature
/// input range, then its hash input range, in signature order.
pub const SHARED: [(Range<usize>, Range<usize>); 3] = [
    (sig::ISSUER_DIGEST, hash::ISSUER_DIGEST),
    (sig::DEVICE_X, hash::DEVICE_X),
    (sig::DEVICE_Y, hash::DEVICE_Y),
];

/// Number of signature inputs stored in the hash witness.
pub const SHARED_BITS: usize = sig::DEVICE_Y.end;

// The shared signature inputs are the leading `SHARED_BITS` private inputs,
// and each pair has equal widths.
const _: () = {
    let mut i = 0;
    let mut next = 0;
    while i < SHARED.len() {
        let (s, h) = (&SHARED[i].0, &SHARED[i].1);
        assert!(s.start == next && s.end - s.start == h.end - h.start);
        next = s.end;
        i += 1;
    }
    assert!(next == SHARED_BITS);
};

/// Fail unless an encoder or allocator at `position` is at the start of `range`.
pub fn check_at(position: usize, range: &Range<usize>, name: &str) -> Result<(), String> {
    if position == range.start {
        Ok(())
    } else {
        Err(format!(
            "mdoc input layout: {name} at {position}, expected {}",
            range.start
        ))
    }
}
