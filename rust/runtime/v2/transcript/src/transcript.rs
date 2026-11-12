// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 transcript sessions. begin_squeeze consumes the writer, and only closing
//! the reader produces the completion token required by round().
//! The session is exclusively borrowed throughout, including on error paths.
//! Complete-proof encoders append a final seal over the chained transcript and
//! canonical proof body; complete verification must check that final seal.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use super::strand::Reader;
use super::Strand;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::algebra::SupportsSampling,
};

/// Joint participant construction rejects field encodings wider than this stack buffer.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub(in crate::runtime::v2) const MAX_FIELD_BYTES: usize = 128;

// Schedule instrumentation has no storage or behavior in production builds.
#[cfg(test)]
#[derive(Default)]
struct RoundCount(u64);
#[cfg(not(test))]
type RoundCount = ();

/// A ready session. It never implements RandomEngine or Clone.
pub struct Transcript {
    strand: Strand,
    _round_count: RoundCount,
}
/// Borrowed protocol operations on one owned session. This capability cannot
/// expose, replace, reset or finalize its owner's transcript.
pub struct TranscriptRef<'a> {
    session: &'a mut Transcript,
}
#[cfg_attr(any(test, feature = "prover", feature = "verifier"), doc = include_str!("../tests/compile_fail.md"))]
/// Exclusive permission to bind messages before the round query.
pub struct Writing<'a> {
    session: &'a mut Transcript,
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    label: u8,
}
/// Exclusive permission to read the finalized strand's PRF stream.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub struct Reading<'a> {
    session: &'a mut Transcript,
    reader: Reader,
}
/// Only end_round constructs this token; round consumes it before releasing
/// the session. Its borrow cannot escape through the round's return value.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[must_use]
pub struct RoundEnd<'a, T> {
    _session: &'a mut Transcript,
    _value: T,
}
impl Transcript {
    pub fn new(context: &[u8]) -> Self {
        let mut t = Self {
            strand: Strand::new(),
            _round_count: Default::default(),
        };
        t.absorb(|w| {
            w.write_bytes(b"longfellow/transcript/v2/strands/v1");
            w.write_bytes(context);
        });
        t
    }
    pub(crate) fn borrow(&mut self) -> TranscriptRef<'_> {
        TranscriptRef { session: self }
    }
    /// Bind setup or terminal messages without sampling. The borrowed writer
    /// cannot be consumed to begin_squeeze; only round grants that capability.
    pub(crate) fn absorb<T>(&mut self, f: impl FnOnce(&mut Writing<'_>) -> T) -> T {
        self.borrow().absorb(f)
    }
    /// The higher-ranked closure must close the exact round it was given.
    /// Dropping or forgetting its capability cannot manufacture a RoundEnd.
    #[cfg(test)]
    pub(crate) fn round<T>(
        &mut self,
        label: impl Into<u8>,
        f: impl for<'r> FnOnce(Writing<'r>) -> RoundEnd<'r, T>,
    ) -> T {
        self.borrow().round(label, f)
    }
    pub(super) fn compute_final_seal(mut self, body: &[u8]) -> [u8; 32] {
        self.absorb(|w| {
            w.write_bytes(b"longfellow/transcript/v2/final");
            w.write_bytes(body);
        });
        self.strand.end_strand().next_block()
    }
}
impl TranscriptRef<'_> {
    pub(crate) fn absorb<T>(&mut self, f: impl FnOnce(&mut Writing<'_>) -> T) -> T {
        f(&mut Writing {
            session: self.session,
            #[cfg(any(test, feature = "prover", feature = "verifier"))]
            // Bind-only writers cannot be consumed to start a reading phase.
            label: 0,
        })
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn round<T>(
        &mut self,
        label: impl Into<u8>,
        f: impl for<'r> FnOnce(Writing<'r>) -> RoundEnd<'r, T>,
    ) -> T {
        f(Writing {
            session: self.session,
            label: label.into(),
        })
        ._value
    }
}
impl Writing<'_> {
    pub fn write_bytes(&mut self, bytes: &[u8]) {
        self.session.strand.write(&[0]);
        self.session
            .strand
            .write(&(bytes.len() as u64).to_le_bytes());
        self.session.strand.write(bytes);
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl Writing<'_> {
    pub fn write_elt_field<F: SerializableField>(&mut self, e: &ElementOf<F>, f: &F) {
        self.session.strand.write(&[1]);
        self.field(e, f);
    }
    pub fn write_elt_field_slice<F: SerializableField>(&mut self, e: &[ElementOf<F>], f: &F) {
        self.session.strand.write(&[2]);
        self.session.strand.write(&(e.len() as u64).to_le_bytes());
        for x in e {
            self.field(x, f);
        }
    }
    fn field<F: SerializableField>(&mut self, e: &ElementOf<F>, f: &F) {
        let mut buf = [0u8; MAX_FIELD_BYTES];
        let n = f.serialized_size_bytes();
        f.to_bytes_into(e, &mut buf[..n]);
        self.session.strand.write(&buf[..n]);
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl<'a> Writing<'a> {
    pub fn begin_squeeze(mut self) -> Reading<'a> {
        self.write_bytes(b"longfellow/transcript/v2/round");
        self.write_bytes(&[self.label]);
        #[cfg(test)]
        {
            self.session._round_count.0 += 1;
        }
        // Finalize exactly once, then start a fresh one-parent continuation. The
        // parent digest stays private; PRF block zero supplies challenges rather
        // than being consumed for a separate link. The owned strand advances
        // without temporarily replacing the session with a fresh root.
        let prf = self.session.strand.continue_in_place();
        Reading {
            session: self.session,
            reader: Reader::new(prf),
        }
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl<'a> Reading<'a> {
    /// Close the reading phase and return a value to the round caller.
    /// The returned value is not absorbed into the transcript.
    pub fn end_round<T>(self, value: T) -> RoundEnd<'a, T> {
        RoundEnd {
            _session: self.session,
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
