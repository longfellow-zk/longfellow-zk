// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Fixed-width words for adapter quotients and their one-time pads.
//!
//! `Word<N>` is an unsigned N-bit integer that exists only inside the adapter.
//! `Otp<N>` is a uniform pad committed with the binary witness. The proof
//! carries only `MaskedWord<N>`: an element of GF(2)^N, neither an integer nor
//! a field element, whose canonical encoding is defined once here.
use crate::runtime::random::RandomEngine;

const fn mask(n: usize) -> u64 {
    if n == 64 {
        u64::MAX
    } else {
        (1u64 << n) - 1
    }
}

/// An unsigned integer below `2^N`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Word<const N: usize>(u64);
impl<const N: usize> Word<N> {
    const WIDTH_OK: () = assert!(N >= 1 && N <= 64, "word width must be 1..=64");
    pub fn new(value: u64) -> Result<Self, String> {
        let () = Self::WIDTH_OK;
        if value & !mask(N) != 0 {
            return Err(format!("value exceeds a {N}-bit word"));
        }
        Ok(Self(value))
    }
    pub fn value(self) -> u64 {
        self.0
    }
}

/// A committed uniform pad for one `Word<N>`. Only the prover constructs it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Otp<const N: usize>(u64);
impl<const N: usize> Otp<N> {
    pub fn sample(rng: &mut impl RandomEngine) -> Self {
        let () = Word::<N>::WIDTH_OK;
        // Exactly ceil(N/8) fresh bytes; the unused high bits are discarded.
        let mut buf = [0u8; 8];
        buf[..N.div_ceil(8)].copy_from_slice(&rng.bytes(N.div_ceil(8)));
        Self(u64::from_le_bytes(buf) & mask(N))
    }
    /// Pad bits, least significant first, for placement in the witness.
    pub fn bits(&self) -> impl Iterator<Item = bool> + '_ {
        (0..N).map(|j| (self.0 >> j) & 1 != 0)
    }
}

/// The published response `k xor o`, an element of GF(2)^N.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaskedWord<const N: usize>(u64);
impl<const N: usize> MaskedWord<N> {
    /// Encoded length: N bits, least significant first, zero-padded to bytes.
    pub const BYTES: usize = N.div_ceil(8);
    pub fn mask(k: Word<N>, o: &Otp<N>) -> Self {
        Self(k.0 ^ o.0)
    }
    pub fn bit(self, j: usize) -> bool {
        assert!(j < N);
        (self.0 >> j) & 1 != 0
    }
    pub fn write(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.0.to_le_bytes()[..Self::BYTES]);
    }
    /// Reject truncated input and any nonzero padding bit.
    pub fn read(bytes: &mut &[u8]) -> Result<Self, String> {
        let () = Word::<N>::WIDTH_OK;
        let (head, tail) = bytes
            .split_at_checked(Self::BYTES)
            .ok_or("truncated masked word")?;
        let mut buf = [0u8; 8];
        buf[..Self::BYTES].copy_from_slice(head);
        let value = u64::from_le_bytes(buf);
        if value & !mask(N) != 0 {
            return Err("noncanonical masked word".into());
        }
        *bytes = tail;
        Ok(Self(value))
    }
    /// The bytes absorbed into the transcript: the canonical encoding.
    pub fn encoded(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(Self::BYTES);
        self.write(&mut out);
        out
    }
}
