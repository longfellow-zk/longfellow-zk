// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Constants of mdoc's cross-field link. The protocol itself lives in the
//! foreign storage layer (`runtime::v2::foreign`), whose README describes it.
//!
//! The signature circuit reads 768 values stored as bits in the hash
//! commitment: the issuer digest and the device public key coordinates.

/// P-256 coordinate modulus, little-endian limbs. The scalar order differs.
#[cfg(any(test, feature = "compiler"))]
pub(crate) const MODULUS: [u64; 4] = [
    0xffffffffffffffff,
    0x00000000ffffffff,
    0,
    0xffffffff00000001,
];
/// Signature-circuit inputs stored in the binary commitment.
pub(crate) const SHARED_BITS: usize = 768;
/// Bits of the mixed split's mask R.
pub(crate) const MASK_BITS: usize = 256;
/// Quotient width: the link claim reads `SHARED_BITS + MASK_BITS = 2^10` bits.
pub(crate) const QUOTIENT_BITS: usize = 10;
const _: () = assert!(SHARED_BITS + MASK_BITS <= 1 << QUOTIENT_BITS);
