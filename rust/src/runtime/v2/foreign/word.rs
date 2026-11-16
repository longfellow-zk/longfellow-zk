// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Fixed-width words for adapter quotients and their one-time pads.
//!
//! `Word<N>` is an unsigned N-bit integer, crate-private and present only in
//! prover builds. `Otp<N>` is a uniform pad committed with the binary
//! witness. The proof carries only `MaskedWord<N>`: an element of GF(2)^N,
//! neither an integer nor a field element, whose canonical encoding is
//! defined once here.
#[cfg(any(test, feature = "prover"))]
use crate::runtime::random::PrivateRandom;
use crate::runtime::v2::proto::composed::AdapterMessage;

#[cfg(any(test, feature = "prover", feature = "verifier"))]
const fn mask(n: usize) -> u64 {
    if n == 64 {
        u64::MAX
    } else {
        (1u64 << n) - 1
    }
}

/// An unsigned integer below `2^N`: an honest adapter quotient. Only the
/// prover builds one.
///
/// The quotient is unmasked, so its `Debug` output omits the value.
#[cfg(any(test, feature = "prover"))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Word<const N: usize>(u64);
#[cfg(any(test, feature = "prover"))]
impl<const N: usize> std::fmt::Debug for Word<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Word").finish_non_exhaustive()
    }
}
#[cfg(any(test, feature = "prover"))]
impl<const N: usize> Word<N> {
    pub(crate) fn new(value: u64) -> Result<Self, String> {
        let () = MaskedWord::<N>::WIDTH_OK;
        if value & !mask(N) != 0 {
            return Err(format!("value exceeds a {N}-bit word"));
        }
        Ok(Self(value))
    }
    #[cfg(test)]
    pub(crate) fn value(self) -> u64 {
        self.0
    }
}

/// A committed uniform pad for one `Word<N>`. Only the prover constructs it,
/// fresh for each proof (`Otp::sample` exists only in prover builds). It is
/// neither `Copy` nor `Clone`, and `MaskedWord::mask` consumes it, so one pad
/// masks exactly one word: two words masked with one pad would publish their
/// XOR (`otp_is_neither_copy_nor_clone`). Its `Debug` output omits the value.
#[derive(PartialEq, Eq)]
pub(crate) struct Otp<const N: usize>(u64);
impl<const N: usize> std::fmt::Debug for Otp<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Otp").finish_non_exhaustive()
    }
}
impl<const N: usize> Otp<N> {
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn sample(rng: &mut impl PrivateRandom) -> Self {
        let () = MaskedWord::<N>::WIDTH_OK;
        // Exactly ceil(N/8) fresh bytes; the unused high bits are discarded.
        let mut buf = [0u8; 8];
        buf[..N.div_ceil(8)].copy_from_slice(&rng.bytes(N.div_ceil(8)));
        Self(u64::from_le_bytes(buf) & mask(N))
    }
    /// Pad bits, least significant first, for placement in the witness.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn bits(&self) -> impl Iterator<Item = bool> + '_ {
        (0..N).map(|j| (self.0 >> j) & 1 != 0)
    }
}

/// The published response `k xor o`, an element of GF(2)^N.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MaskedWord<const N: usize>(u64);
impl<const N: usize> MaskedWord<N> {
    const WIDTH_OK: () = assert!(N >= 1 && N <= 64, "word width must be 1..=64");
    /// Encoded length: N bits, least significant first, zero-padded to bytes.
    pub(crate) const BYTES: usize = {
        let () = Self::WIDTH_OK;
        N.div_ceil(8)
    };
    /// Mask `k` with the pad `o`, which this consumes.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn mask(k: Word<N>, o: Otp<N>) -> Self {
        Self(k.0 ^ o.0)
    }
    pub(crate) fn bit(self, j: usize) -> bool {
        assert!(j < N);
        (self.0 >> j) & 1 != 0
    }
    #[cfg(any(test, feature = "prover"))]
    fn write(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.0.to_le_bytes()[..Self::BYTES]);
    }
    /// Reject truncated input and any nonzero padding bit. A component
    /// reader, called only through the composed body's reader (proto I2).
    #[cfg(any(test, feature = "verifier"))]
    pub(crate) fn read(bytes: &mut &[u8]) -> Result<Self, String> {
        let () = Self::WIDTH_OK;
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
    /// The word's canonical proof-body encoding, as the body writer emits it.
    /// The transcript absorbs the word's bits through the
    /// `P256AdapterQuotients` message instead.
    #[cfg(test)]
    pub(crate) fn encoded(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(Self::BYTES);
        self.write(&mut out);
        out
    }
}

impl<const N: usize> AdapterMessage for [MaskedWord<N>; 2] {
    const BYTES: usize = 2 * MaskedWord::<N>::BYTES;
    #[cfg(any(test, feature = "prover"))]
    fn write(&self, out: &mut Vec<u8>) {
        for m in self {
            m.write(out);
        }
    }
    #[cfg(any(test, feature = "verifier"))]
    fn read(b: &mut &[u8]) -> Result<Self, String> {
        Ok([MaskedWord::read(b)?, MaskedWord::read(b)?])
    }
}
