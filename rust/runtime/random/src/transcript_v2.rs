// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 transcript sessions. Round capabilities are affine: begin_squeeze consumes the
//! writer, and only closing the reader produces the token required by round().
//! The session is exclusively borrowed throughout, including on error paths.
//! Complete-proof encoders append a final seal over the chained transcript and
//! canonical proof body; complete verification must check that final seal.
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::algebra::SupportsSampling,
};
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256, Shake256Reader,
};

/// Closed protocol roles; these labels are part of the v2 transcript format.
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum RoundLabel {
    Output = 0,
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
#[doc = include_str!("../tests/transcript_v2_compile_fail.md")]
/// Exclusive permission to bind messages before the round query.
pub struct Writing<'a> {
    core: &'a mut Core,
    label: RoundLabel,
}
/// Exclusive permission to squeeze challenges from the boundary answer.
pub struct Reading<'a> {
    core: &'a mut Core,
    reader: Shake256Reader,
}
/// Only end_round constructs this token; round consumes it before releasing
/// the session. Its borrow cannot escape through the round's return value.
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
    /// Bind setup or terminal messages without sampling. The borrowed writer
    /// cannot be consumed to begin_squeeze; only round grants that capability.
    pub(crate) fn bind<T>(&mut self, f: impl FnOnce(&mut Writing<'_>) -> T) -> T {
        f(&mut Writing {
            core: &mut self.core,
            label: RoundLabel::Statement,
        })
    }
    /// The higher-ranked closure must close the exact round it was given.
    /// Dropping or forgetting its capability cannot manufacture a RoundEnd.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn round<T>(
        &mut self,
        label: RoundLabel,
        f: impl for<'r> FnOnce(Writing<'r>) -> RoundEnd<'r, T>,
    ) -> T {
        let end = f(Writing {
            core: &mut self.core,
            label,
        });
        end._value
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
impl Writing<'_> {
    pub fn write_bytes(&mut self, bytes: &[u8]) {
        self.core.hash.update(&[0]);
        self.core.hash.update(&(bytes.len() as u64).to_le_bytes());
        self.core.hash.update(bytes);
    }
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
        let mut buf = [0u8; 128];
        let n = f.serialized_size_bytes();
        f.to_bytes_into(e, &mut buf[..n]);
        self.core.hash.update(&buf[..n]);
    }
}
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
        let bits = usize::BITS - n.leading_zeros();
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
#[path = "../tests/transcript_v2.rs"]
mod tests;

mod prover;
mod verifier;
pub use prover::EncodedProof;
pub use verifier::{Unverified, VerifiedProof};
