// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 transcript sessions. Round capabilities are affine: begin_squeeze consumes the
//! writer, and only closing the reader produces the token required by round().
//! The session is exclusively borrowed throughout, including on error paths.
//! Complete-proof encoders append a final seal over the chained transcript and
//! canonical proof body; complete verification must check that final seal.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use sha3::Shake256Reader;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::algebra::SupportsSampling,
};

/// Joint participant construction rejects field encodings wider than this stack buffer.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(in crate::runtime::v2) const MAX_FIELD_BYTES: usize = 128;

/// Closed protocol roles; these labels are part of the v2 transcript format.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum RoundLabel {
    // Tag 0 is reserved; circuit outputs join their layer's assertion round.
    Assertions = 1,
    Sumcheck = 2,
    Terminal = 3,
    Combine = 4,
    Packing = 5,
    Statement = 6,
    Batching = 7,
    Opening = 8,
    Rescaling = 9,
    Conversion = 10,
    RowBatching = 11,
    Fingerprint = 12,
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl RoundLabel {
    fn tag(self) -> u8 {
        self as u8
    }
}
struct Core {
    hash: Shake256,
    rounds: u64,
}
/// A ready session. It never implements RandomEngine or Clone.
pub struct Transcript {
    core: Core,
}
/// Borrowed protocol operations on one owned session. This capability cannot
/// expose, replace, reset or finalize its owner's transcript.
pub struct TranscriptRef<'a> {
    core: &'a mut Core,
}
#[cfg_attr(any(test, feature = "prover", feature = "verifier"), doc = include_str!("../tests/compile_fail.md"))]
/// Exclusive permission to bind messages before the round query.
pub struct Writing<'a> {
    core: &'a mut Core,
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    label: RoundLabel,
}
/// Exclusive permission to squeeze challenges from the boundary answer.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub struct Reading<'a> {
    core: &'a mut Core,
    reader: Shake256Reader,
}
/// Only end_round constructs this token; round consumes it before releasing
/// the session. Its borrow cannot escape through the round's return value.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[must_use]
pub struct RoundEnd<'a, T> {
    _core: &'a mut Core,
    _value: T,
}
impl Transcript {
    pub fn new(context: &[u8]) -> Self {
        let mut t = Self {
            core: Core {
                hash: Shake256::default(),
                rounds: 0,
            },
        };
        t.bind(|w| {
            w.write_bytes(b"longfellow/transcript/v2");
            w.write_bytes(context);
        });
        t
    }
    pub(crate) fn borrow(&mut self) -> TranscriptRef<'_> {
        TranscriptRef {
            core: &mut self.core,
        }
    }
    /// Bind setup or terminal messages without sampling. The borrowed writer
    /// cannot be consumed to begin_squeeze; only round grants that capability.
    pub(crate) fn bind<T>(&mut self, f: impl FnOnce(&mut Writing<'_>) -> T) -> T {
        self.borrow().bind(f)
    }
    /// The higher-ranked closure must close the exact round it was given.
    /// Dropping or forgetting its capability cannot manufacture a RoundEnd.
    #[cfg(test)]
    pub(crate) fn round<T>(
        &mut self,
        label: RoundLabel,
        f: impl for<'r> FnOnce(Writing<'r>) -> RoundEnd<'r, T>,
    ) -> T {
        self.borrow().round(label, f)
    }
    fn compute_final_seal(mut self, body: &[u8]) -> [u8; 32] {
        let rounds = self.core.rounds;
        self.bind(|w| {
            w.write_bytes(b"longfellow/transcript/v2/final");
            w.write_bytes(&rounds.to_le_bytes());
            w.write_bytes(body);
        });
        let mut reader = self.core.hash.finalize_xof();
        let mut final_seal = [0; 32];
        reader.read(&mut final_seal);
        final_seal
    }
}
impl TranscriptRef<'_> {
    pub(crate) fn bind<T>(&mut self, f: impl FnOnce(&mut Writing<'_>) -> T) -> T {
        f(&mut Writing {
            core: self.core,
            #[cfg(any(test, feature = "prover", feature = "verifier"))]
            label: RoundLabel::Statement,
        })
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn round<T>(
        &mut self,
        label: RoundLabel,
        f: impl for<'r> FnOnce(Writing<'r>) -> RoundEnd<'r, T>,
    ) -> T {
        f(Writing {
            core: self.core,
            label,
        })
        ._value
    }
}
impl Writing<'_> {
    pub fn write_bytes(&mut self, bytes: &[u8]) {
        self.core.hash.update(&[0]);
        self.core.hash.update(&(bytes.len() as u64).to_le_bytes());
        self.core.hash.update(bytes);
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl Writing<'_> {
    pub fn write_elt_field<F: SerializableField>(&mut self, e: &ElementOf<F>, f: &F) {
        self.core.hash.update(&[1]);
        self.field(e, f);
    }
    pub fn write_elt_field_slice<F: SerializableField>(&mut self, e: &[ElementOf<F>], f: &F) {
        self.core.hash.update(&[2]);
        self.core.hash.update(&(e.len() as u64).to_le_bytes());
        for x in e {
            self.field(x, f);
        }
    }
    fn field<F: SerializableField>(&mut self, e: &ElementOf<F>, f: &F) {
        let mut buf = [0u8; MAX_FIELD_BYTES];
        let n = f.serialized_size_bytes();
        f.to_bytes_into(e, &mut buf[..n]);
        self.core.hash.update(&buf[..n]);
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl<'a> Writing<'a> {
    pub fn begin_squeeze(mut self) -> Reading<'a> {
        self.write_bytes(b"longfellow/transcript/v2/round");
        self.write_bytes(&[self.label.tag()]);
        self.write_bytes(&self.core.rounds.to_le_bytes());
        self.core.rounds = self
            .core
            .rounds
            .checked_add(1)
            .expect("too many transcript rounds");
        // One direct XOF oracle answer supplies both the link and challenges.
        // The snapshot is private. Absorb the actual first output bytes into
        // the continuing accumulator, then retain this SAME reader at offset 32.
        let mut reader = self.core.hash.clone().finalize_xof();
        let mut link = [0; 32];
        reader.read(&mut link);
        self.write_bytes(b"longfellow/transcript/v2/boundary-output");
        self.write_bytes(&link);
        Reading {
            core: self.core,
            reader,
        }
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl<'a> Reading<'a> {
    /// Close the reading phase and return a value to the round caller.
    /// The returned value is not absorbed into the transcript.
    pub fn end_round<T>(self, value: T) -> RoundEnd<'a, T> {
        RoundEnd {
            _core: self.core,
            _value: value,
        }
    }
    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        let mut bytes = vec![0; n];
        self.reader.read(&mut bytes);
        bytes
    }
    pub fn elt_field<F: SupportsSampling>(&mut self, f: &F) -> F::E {
        f.sample(|n| self.bytes(n))
    }
    pub fn elt_field_slice<F: SupportsSampling>(&mut self, n: usize, f: &F) -> Vec<F::E> {
        (0..n).map(|_| self.elt_field(f)).collect()
    }
    pub fn choose(&mut self, out: &mut [usize], n: usize, k: usize) {
        assert!(n >= k && out.len() >= k);
        let mut a: Vec<_> = (0..n).collect();
        for i in 0..k {
            let j = i + self.nat(n - i);
            a.swap(i, j);
            out[i] = a[i];
        }
    }
    fn nat(&mut self, n: usize) -> usize {
        assert!(n > 0);
        if n == 1 {
            return 0;
        }
        // Mask the largest admissible value. Powers of two need no rejection.
        let bits = usize::BITS - (n - 1).leading_zeros();
        let len = bits.div_ceil(8) as usize;
        let mask = usize::MAX >> (usize::BITS - bits);
        loop {
            let mut bytes = [0u8; size_of::<usize>()];
            bytes[..len].copy_from_slice(&self.bytes(len));
            let x = usize::from_le_bytes(bytes) & mask;
            if x < n {
                return x;
            }
        }
    }
}
#[cfg(test)]
#[path = "../tests/transcript.rs"]
mod tests;

mod prover;
mod verifier;
pub use prover::EncodedProof;
pub use verifier::{Unverified, VerifiedProof};
