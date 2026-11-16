// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Named input positions and public-input counts of the mdoc v2 circuits,
//! shared by the circuit compiler, the witness encoders and the runtime link.
//!
//! Positions are relative to each circuit's public prefix. The signature
//! circuit stores its first private inputs, one input per bit, as bits of the
//! hash circuit's witness; `SHARED` pairs each such signature range with its
//! hash range. Both circuits allocate the shared values first, in the same
//! order, so each pair names the same private offsets. The compiler and the
//! encoders check their allocation order against these ranges, and the link
//! reads them, so this table is the single description of the shared positions.
use core::ops::Range;

use super::{
    hash::constants::{
        K_DOC_TYPE_BYTES, K_HASH_INDEX_BITS, K_MSO_PREIMAGE_LEN, K_NAMESPACE_BYTES,
        K_TIMESTAMP_DIGITS,
    },
    mso_attribute::constants::{K_ATTR_ID_BYTES, K_ATTR_INDEX_BITS, K_ATTR_VALUE_BYTES},
};

const fn after(previous: Range<usize>, width: usize) -> Range<usize> {
    previous.end..previous.end + width
}

/// Public-input counts of both circuits (mdoc v2 DESIGN.md I3), in
/// allocation order. Each byte is 8 inputs and each length
/// `K_ATTR_INDEX_BITS` inputs.
pub mod public {
    use super::{
        K_ATTR_ID_BYTES, K_ATTR_INDEX_BITS, K_ATTR_VALUE_BYTES, K_DOC_TYPE_BYTES,
        K_NAMESPACE_BYTES, K_TIMESTAMP_DIGITS,
    };
    /// The hash circuit's leading time: its 14 digits.
    const HASH_TIME: usize = 8 * K_TIMESTAMP_DIGITS.len();
    /// Each attribute of the hash circuit: its CBOR identifier and its CBOR
    /// value, each with its length.
    pub const HASH_PER_ATTRIBUTE: usize =
        8 * K_ATTR_ID_BYTES + K_ATTR_INDEX_BITS + 8 * K_ATTR_VALUE_BYTES + K_ATTR_INDEX_BITS;
    /// The hash circuit's inputs after the attributes: the document-type
    /// flag, then the document type and the namespace, each with its length.
    const HASH_TRAILER: usize =
        1 + 8 * K_DOC_TYPE_BYTES + K_ATTR_INDEX_BITS + 8 * K_NAMESPACE_BYTES + K_ATTR_INDEX_BITS;
    /// The hash circuit's inputs other than the attributes: it has
    /// `HASH_FIXED + HASH_PER_ATTRIBUTE * A` for A attributes.
    pub const HASH_FIXED: usize = HASH_TIME + HASH_TRAILER;
    /// The signature circuit's: the issuer key's two coordinates and the 256
    /// bits of `e2`.
    pub const SIGNATURE: usize = 2 + 256;

    // The counts DESIGN.md I3 states; changing one changes the circuits.
    const _: () = assert!(HASH_FIXED == 901 && HASH_PER_ATTRIBUTE == 788 && SIGNATURE == 258);
}

/// The hash circuit's leading private inputs, in allocation order.
pub mod hash {
    use super::{after, Range, K_HASH_INDEX_BITS, K_MSO_PREIMAGE_LEN};
    pub const ISSUER_DIGEST: Range<usize> = 0..256;
    pub const DEVICE_X: Range<usize> = after(ISSUER_DIGEST, 256);
    pub const DEVICE_Y: Range<usize> = after(DEVICE_X, 256);
    pub const MSO_PREIMAGE: Range<usize> = after(DEVICE_Y, 8 * K_MSO_PREIMAGE_LEN);
    pub const MSO_LEN: Range<usize> = after(MSO_PREIMAGE, K_HASH_INDEX_BITS);
    pub const NBLOCKS: Range<usize> = after(MSO_LEN, 8);
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

// The shared values are the leading `SHARED_BITS` private inputs of both
// circuits, at the same offsets.
const _: () = {
    let mut i = 0;
    let mut next = 0;
    while i < SHARED.len() {
        let (s, h) = (&SHARED[i].0, &SHARED[i].1);
        assert!(s.start == next && s.start == h.start && s.end == h.end);
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
