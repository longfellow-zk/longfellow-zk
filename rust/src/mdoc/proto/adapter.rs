// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Constants of mdoc's composition, shared by its circuits and runtime.
//! Storage maps and the split live in `runtime::v2::zk`, the adapter and the
//! driver in `runtime::v2::foreign`.
//!
//! The signature circuit reads 768 values stored as bits in the hash
//! commitment: the issuer digest and the device public key coordinates.

/// Signature-circuit inputs stored in the binary commitment.
pub(crate) const SHARED_BITS: usize = super::layout::SHARED_BITS;
/// Bits of the mixed split's mask R.
pub(crate) const MASK_BITS: usize = 256;
/// Quotient width: the link claim reads `SHARED_BITS + MASK_BITS = 2^10` bits.
pub(crate) const QUOTIENT_BITS: usize = 10;
const _: () = assert!(SHARED_BITS + MASK_BITS <= 1 << QUOTIENT_BITS);
