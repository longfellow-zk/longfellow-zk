// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! SHA-256 strands with private finalized states. Continuing consumes an
//! absorbing strand and returns its PRF and a fresh one-parent strand.
//!
//! All integers are little endian. Nodes absorb
//! `u32(STRAND) || u64(id) || u32(parent_count) || parent`, followed by raw
//! message bytes. The root has id zero and no parent. Each continuation has
//! one parent and increments its id without wrapping. Thus distinct positions
//! in a chain have distinct hash inputs, even if their parent digests collide.
//! PRF blocks hash `u32(PRF) || u64(id) || parent || u64(counter)`. The id and
//! checked block counter distinguish every block, even if node digests collide.
//! The type tags separate all PRF and strand inputs, including empty roots
//! and empty child messages.
//! Finalized states use ordinary SHA-256 padding and never leave this module.

use sha2::{Digest, Sha256};

const PRF: u32 = 0;
const STRAND: u32 = 1;
const BLOCK_BYTES: usize = 32;

/// An absorbing strand. Finalization consumes it; it cannot be cloned or reset.
#[doc = include_str!("../tests/strand_compile_fail.md")]
#[must_use = "a strand must be continued or finalized to obtain its PRF"]
pub struct Strand {
    hash: Sha256,
    id: u64,
}

/// Expands a finalized strand into independently indexed 32-byte blocks.
pub struct Prf {
    id: u64,
    parent: [u8; BLOCK_BYTES],
    counter: u64,
}

impl Strand {
    /// Start a zero-parent root; bind its initializer and context as messages.
    pub fn new() -> Self {
        Self::with_parent(0, None)
    }

    fn with_parent(id: u64, parent: Option<&[u8; BLOCK_BYTES]>) -> Self {
        let mut hash = Sha256::new();
        hash.update(STRAND.to_le_bytes());
        hash.update(id.to_le_bytes());
        hash.update(u32::from(parent.is_some()).to_le_bytes());
        if let Some(digest) = parent {
            hash.update(digest);
        }
        Self { hash, id }
    }

    /// Append raw bytes. Splitting a write does not change the hashed message.
    pub fn write(&mut self, bytes: &[u8]) {
        self.hash.update(bytes);
    }

    /// Finish with ordinary SHA-256 padding, keeping the resulting digest private.
    #[must_use]
    pub fn end_strand(self) -> Prf {
        let parent = self.hash.finalize().into();
        Prf {
            id: self.id,
            parent,
            counter: 0,
        }
    }

    /// Finish this node and start a fresh node with its digest as the sole parent.
    /// Challenge reads do not change the continuation, and the digest stays private.
    pub fn continue_strand(mut self) -> (Prf, Self) {
        let prf = self.continue_in_place();
        (prf, self)
    }

    // The typed transcript owns the strand during this transition. Check the id
    // before changing state so even a caught overflow cannot restart the chain.
    pub(super) fn continue_in_place(&mut self) -> Prf {
        let id = self.id.checked_add(1).expect("strand id exhausted");
        let prf = Prf {
            id: self.id,
            parent: self.hash.finalize_reset().into(),
            counter: 0,
        };
        *self = Self::with_parent(id, Some(&prf.parent));
        prf
    }
}

impl Default for Strand {
    fn default() -> Self {
        Self::new()
    }
}

impl Prf {
    /// Return SHA256(PRF || id || parent || counter), then advance the counter.
    pub fn next_block(&mut self) -> [u8; BLOCK_BYTES] {
        let counter = self.counter;
        self.counter = counter
            .checked_add(1)
            .expect("strand PRF counter exhausted");
        // The complete preimage fits in one padded SHA-256 block. Caching an
        // incremental hasher would save no compression and would retain more state.
        let mut input = [0u8; 4 + 8 + BLOCK_BYTES + 8];
        input[..4].copy_from_slice(&PRF.to_le_bytes());
        input[4..12].copy_from_slice(&self.id.to_le_bytes());
        input[12..12 + BLOCK_BYTES].copy_from_slice(&self.parent);
        input[12 + BLOCK_BYTES..].copy_from_slice(&counter.to_le_bytes());
        Sha256::digest(input).into()
    }
}

/// Byte cursor used by a round. Keep unread block tails across sampling calls;
/// closing the round drops the cursor and cannot rewind its PRF.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(super) struct Reader {
    prf: Prf,
    block: [u8; BLOCK_BYTES],
    offset: usize,
}

#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl Reader {
    pub(super) fn new(prf: Prf) -> Self {
        Self {
            prf,
            block: [0; BLOCK_BYTES],
            offset: BLOCK_BYTES,
        }
    }

    pub(super) fn read(&mut self, mut out: &mut [u8]) {
        while !out.is_empty() {
            if self.offset == BLOCK_BYTES {
                self.block = self.prf.next_block();
                self.offset = 0;
            }
            let count = out.len().min(BLOCK_BYTES - self.offset);
            out[..count].copy_from_slice(&self.block[self.offset..self.offset + count]);
            self.offset += count;
            out = &mut out[count..];
        }
    }
}

#[cfg(test)]
#[path = "../tests/strand.rs"]
mod tests;
