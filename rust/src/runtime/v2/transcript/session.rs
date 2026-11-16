// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 transcript sessions.
//!
//! A session opens with its statement (transcript I1). After it, protocol
//! code only sends prover messages and draws challenges, both through a
//! borrowed `TranscriptRef`. A strand node is
//!
//! ```text
//! node := message+ end
//! end  := u64(0)   ; ROUND: a draw follows
//!       | u64(1)   ; SEAL: the proof ends
//! ```
//!
//! A draw ends a node only after a message (transcript I7): it writes the
//! ROUND terminator, continues the strand and reads from the finalized
//! node's PRF stream. A draw with no message since the last boundary reads
//! further from that stream, writing nothing. Complete-proof encoders append
//! the seal: the Seal message over every proof byte, the SEAL terminator,
//! then the node's first PRF block; complete verification must check it.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use super::message::ProverMessage;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use super::message::Seal;
#[cfg(any(test, feature = "testonly"))]
use super::message::ZkStatement;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use super::strand::Reader;
use super::{
    message::{Encoder, Message, SetupMessage},
    Strand,
};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
use crate::runtime::algebra::SupportsSampling;

/// A complete proof ends in one final seal: the next block of the ended strand.
pub const SEAL_BYTES: usize = super::strand::BLOCK_BYTES;

/// Node terminators. Tags start at 16, so a terminator is never a tag.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
const ROUND: u64 = 0;
#[cfg(any(test, feature = "prover", feature = "verifier"))]
const SEAL: u64 = 1;

/// The statement a transcript opens with: everything the verifier fixes
/// before it reads a proof byte (transcript I1). The transcript writes its
/// identity message first, then the messages `write` emits, so every
/// statement starts with its identity and the root node is never empty.
pub trait Statement {
    /// The identity message: the protocol ID and what names the instance.
    type Identity: SetupMessage + ?Sized;
    fn identity(&self) -> &Self::Identity;
    /// Write the statement messages after the identity, in their fixed order.
    fn write(&self, h: &mut Header<'_>);
}
/// The writer of a statement. It exists only while `Transcript::new` runs.
pub struct Header<'a> {
    session: &'a mut Transcript,
}
impl Header<'_> {
    pub fn send<M: SetupMessage + ?Sized>(&mut self, m: &M) {
        self.session.send_message(m);
    }
}
/// Alone, `ZkStatement` is the whole statement of a bare transcript (tests,
/// tools), which binds no part a component reads.
#[cfg(any(test, feature = "testonly"))]
impl<'a> Statement for ZkStatement<'a> {
    type Identity = Self;
    fn identity(&self) -> &Self {
        self
    }
    fn write(&self, _: &mut Header<'_>) {}
}

/// A ready session. It never implements RandomEngine, PrivateRandom or Clone.
#[cfg_attr(not(feature = "testonly"), allow(unreachable_pub))]
pub struct Transcript {
    strand: Strand,
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    session: SessionStamp,
    /// The last boundary's PRF stream while no message has been written
    /// since; the next draw continues it (transcript I7).
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    stream: Option<Reader>,
    /// Schedule instrumentation; it has no storage in production builds.
    #[cfg(test)]
    pub(super) trace: super::trace::Trace,
}

/// The identity of one transcript session. The session owns a fresh
/// allocation and every stamp holds a clone of it, so stamps compare by
/// address, and no address is reused while a stamp exists. A protocol state
/// that spans several calls records it at creation and rejects a later call
/// on any other session (transcript I2).
#[cfg(any(test, feature = "prover", feature = "verifier"))]
#[derive(Clone, Debug)]
pub struct SessionStamp(std::sync::Arc<()>);

#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl SessionStamp {
    /// A fresh identity, owned by the session it is created for. It changes
    /// no transcript byte.
    pub(super) fn fresh() -> Self {
        Self(std::sync::Arc::new(()))
    }
    /// The identity of no session, for the static systems of tests and
    /// tools: no session's check accepts it.
    #[cfg(any(test, feature = "testonly"))]
    pub(crate) fn detached() -> Self {
        Self::fresh()
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl PartialEq for SessionStamp {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.0, &other.0)
    }
}
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl Eq for SessionStamp {}
/// Borrowed protocol operations on one owned session. This capability cannot
/// expose, replace, reset or finalize its owner's transcript.
pub struct TranscriptRef<'a> {
    #[cfg_attr(
        not(any(test, feature = "prover", feature = "verifier")),
        allow(dead_code)
    )]
    pub(super) session: &'a mut Transcript,
}
#[cfg_attr(any(test, feature = "prover", feature = "verifier"), doc = include_str!("compile_fail.md"))]
/// Exclusive permission to read the last boundary's PRF stream. It cannot
/// send a message; the session keeps the stream for draws that follow with
/// no message in between.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub struct Reading<'a> {
    reader: &'a mut Reader,
    #[cfg(test)]
    trace: &'a mut super::trace::Trace,
}
impl Transcript {
    /// Open a session with `statement`, the only setup it ever absorbs
    /// (transcript I1): its identity, then its other messages. Outside the
    /// crate a session opens only as an `Opened`, which keeps the statement.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn new<S: Statement + ?Sized>(statement: &S) -> Self {
        let mut t = Self {
            strand: Strand::new(),
            #[cfg(any(test, feature = "prover", feature = "verifier"))]
            session: SessionStamp::fresh(),
            #[cfg(any(test, feature = "prover", feature = "verifier"))]
            stream: None,
            #[cfg(test)]
            trace: Default::default(),
        };
        t.send_message(statement.identity());
        statement.write(&mut Header { session: &mut t });
        t
    }
    /// A bare session for tests and tools: its whole statement is a
    /// `ZkStatement` with `context`.
    #[cfg(any(test, feature = "testonly"))]
    pub fn for_test(context: &[u8]) -> Self {
        Self::new(&ZkStatement { context })
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn borrow(&mut self) -> TranscriptRef<'_> {
        TranscriptRef { session: self }
    }
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(super) fn session(&self) -> SessionStamp {
        self.session.clone()
    }
    /// Write one message: its tag, then its values. A message ends the
    /// current stream: the next draw ends the node.
    pub(super) fn send_message<M: Message + ?Sized>(&mut self, m: &M) {
        #[cfg(any(test, feature = "prover", feature = "verifier"))]
        {
            self.stream = None;
        }
        self.strand.write(&M::TAG.value().to_le_bytes());
        #[cfg(not(test))]
        m.encode(&mut Encoder::new(&mut self.strand));
        #[cfg(test)]
        {
            let mut record = super::message::Recorded {
                tag: M::TAG.value(),
                ..Default::default()
            };
            m.encode(&mut Encoder::new(&mut self.strand, &mut record));
            self.trace.message(record);
        }
    }
    /// Read challenges from the last boundary's stream, ending the node
    /// first if a message was sent since (transcript I7). The closure reads
    /// the stream where the session keeps it, so a panic in it loses no
    /// stream: a caught panic leaves the session after the bytes it read.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(super) fn draw<T>(&mut self, f: impl FnOnce(&mut Reading<'_>) -> T) -> T {
        if self.stream.is_none() {
            self.stream = Some(self.open());
        }
        let Some(reader) = &mut self.stream else {
            unreachable!("the stream was just opened")
        };
        f(&mut Reading {
            reader,
            #[cfg(test)]
            trace: &mut self.trace,
        })
    }
    /// End the node with the ROUND terminator and start a one-parent
    /// continuation. The parent digest stays private; PRF block zero supplies
    /// challenges rather than being consumed for a separate link.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    fn open(&mut self) -> Reader {
        self.strand.write(&ROUND.to_le_bytes());
        #[cfg(test)]
        self.trace
            .boundary(std::mem::take(&mut self.strand.preimage));
        Reader::new(self.strand.continue_in_place())
    }
    /// The seal block over `body`: the Seal message, the SEAL terminator,
    /// then the first PRF block of the sealed node (transcript I10).
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(super) fn compute_final_seal(&mut self, body: &[u8]) -> [u8; SEAL_BYTES] {
        self.send_message(&Seal(body));
        self.strand.write(&SEAL.to_le_bytes());
        #[cfg(test)]
        self.trace.seal(std::mem::take(&mut self.strand.preimage));
        std::mem::take(&mut self.strand).end_strand().next_block()
    }
}
impl TranscriptRef<'_> {
    /// Send one prover message, absorbed exactly once (transcript I4).
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn send<M: ProverMessage + ?Sized>(&mut self, m: &M) {
        self.session.send_message(m);
    }
    /// Draw challenges (transcript I7). The closure reads them in order and
    /// cannot send a message.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn draw<T>(&mut self, f: impl FnOnce(&mut Reading<'_>) -> T) -> T {
        self.session.draw(f)
    }
}
/// The draw kinds. None allocates: an element is sampled into the field's
/// own buffer, `elements` yields its values to the caller, and `choose`
/// works in the caller's storage.
#[cfg(any(test, feature = "prover", feature = "verifier"))]
impl<'a> Reading<'a> {
    /// The next `n` bytes of the stream, for tests that check the stream
    /// itself.
    #[cfg(test)]
    pub(crate) fn bytes(&mut self, n: usize) -> Vec<u8> {
        let mut bytes = vec![0; n];
        self.fill(&mut bytes);
        bytes
    }
    /// Fill `out` with the next bytes of the stream.
    #[cfg(test)]
    pub(crate) fn fill(&mut self, out: &mut [u8]) {
        self.trace.draw(super::trace::Draw::Bytes);
        self.reader.read(out);
    }
    /// element: one element of `f`. A prime field reads its sample byte
    /// count, masks the top byte and rejects values at or above the modulus.
    pub fn elt_field<F: SupportsSampling>(&mut self, f: &F) -> F::E {
        #[cfg(test)]
        self.trace.draw(super::trace::Draw::Element);
        f.sample(|out| self.reader.read(out))
    }
    /// nonzero: `elt_field` repeated until the value is not zero. The test
    /// trace records it as one draw of its own kind.
    pub fn nonzero<F: SupportsSampling>(&mut self, f: &F) -> F::E {
        #[cfg(test)]
        self.trace.draw(super::trace::Draw::Nonzero);
        loop {
            let x = f.sample(|out| self.reader.read(out));
            if !f.is_zero(&x) {
                break x;
            }
        }
    }
    /// elements: `n` independent elements of `f`, in order, read as the
    /// caller takes them.
    pub fn elements<'r, F: SupportsSampling>(
        &'r mut self,
        f: &'r F,
        n: usize,
    ) -> impl Iterator<Item = F::E> + use<'r, 'a, F> {
        (0..n).map(move |_| self.elt_field(f))
    }
    /// indices: `out.len()` distinct indices out of `0..n` by Fisher-Yates
    /// with masked rejection, in `scratch` (at least `n` entries, overwritten).
    pub fn choose(&mut self, out: &mut [usize], n: usize, scratch: &mut [usize]) {
        let k = out.len();
        assert!(n >= k && scratch.len() >= n);
        #[cfg(test)]
        self.trace.draw(super::trace::Draw::Indices);
        let a = &mut scratch[..n];
        for (i, x) in a.iter_mut().enumerate() {
            *x = i;
        }
        for i in 0..k {
            let j = i + self.nat(n - i);
            a.swap(i, j);
            out[i] = a[i];
        }
        #[cfg(test)]
        self.trace.indices(out);
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
            self.reader.read(&mut bytes[..len]);
            let x = usize::from_le_bytes(bytes) & mask;
            if x < n {
                return x;
            }
        }
    }
}
#[cfg(test)]
mod tests;
