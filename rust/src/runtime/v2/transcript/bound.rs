// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Statement-bound transcript capabilities and stamped challenges.
//!
//! A `Bound` pairs a session with the statement part a component reads, so
//! the component uses the values its caller holds next to the transcript
//! (transcript I2). A `Challenge` is a value drawn at one boundary for the
//! next component. Its consumer accepts it only while the session still
//! stands at that boundary, with no message sent since (transcript I8).
use super::session::{Position, RoundEnd, SessionStamp, Transcript, TranscriptRef, Writing};

impl Transcript {
    /// Bind `part`, the statement part a component reads, to this session.
    pub fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P> {
        Bound { part, owner: self }
    }
}

/// A transcript capability bundled with the statement part it refers to.
/// It cannot replace, clone or finalize its owner's session.
pub struct Bound<'a, P: ?Sized> {
    part: &'a P,
    owner: &'a mut Transcript,
}
impl<'a, P: ?Sized> Bound<'a, P> {
    /// The bound statement part.
    pub fn part(&self) -> &'a P {
        self.part
    }
    /// The same session, bound to a part of this part.
    pub fn project<Q: ?Sized + 'a>(&mut self, f: impl FnOnce(&'a P) -> &'a Q) -> Bound<'_, Q> {
        Bound {
            part: f(self.part),
            owner: self.owner,
        }
    }
    /// The session's identity, for states that span several calls.
    pub fn session(&self) -> SessionStamp {
        self.owner.session()
    }
    /// Consume `c` if this session still stands where it was drawn.
    pub fn accept<T>(&self, c: Challenge<T>) -> Result<T, StaleChallenge> {
        c.accept(self.owner.position())
    }
    /// The session's message and round operations.
    pub(crate) fn transcript(&mut self) -> TranscriptRef<'_> {
        self.owner.borrow()
    }
    /// Run a round whose value a later component consumes.
    pub(crate) fn challenge<T>(
        &mut self,
        label: impl Into<u8>,
        f: impl for<'r> FnOnce(Writing<'r>) -> RoundEnd<'r, T>,
    ) -> Challenge<T> {
        self.transcript().challenge(label, f)
    }
}
impl TranscriptRef<'_> {
    /// Run a round whose value a later component consumes, stamped with the
    /// boundary it reads from (transcript I7, I8).
    pub(crate) fn challenge<T>(
        &mut self,
        label: impl Into<u8>,
        f: impl for<'r> FnOnce(Writing<'r>) -> RoundEnd<'r, T>,
    ) -> Challenge<T> {
        let value = self.round(label, f);
        Challenge::stamp(value, self.session.position())
    }
    /// Consume `c` if this session still stands where it was drawn.
    pub(crate) fn accept<T>(&self, c: Challenge<T>) -> Result<T, StaleChallenge> {
        c.accept(self.session.position())
    }
}

#[doc = include_str!("bound_compile_fail.md")]
/// A value drawn from a transcript, stamped with the boundary it came from:
/// the node index, a private copy of that node's digest, and the session's
/// message count. It is not `Clone`, and accepting it consumes it.
#[must_use = "a challenge is drawn for a consumer that must accept it"]
pub struct Challenge<T> {
    value: T,
    at: Position,
}
impl<T> Challenge<T> {
    fn stamp(value: T, at: Position) -> Self {
        Self { value, at }
    }
    fn accept(self, now: Position) -> Result<T, StaleChallenge> {
        if self.at == now {
            Ok(self.value)
        } else {
            Err(StaleChallenge)
        }
    }
}

/// A challenge was drawn at another boundary or on another transcript, or a
/// message was sent after it was drawn.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StaleChallenge;
impl std::fmt::Display for StaleChallenge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("challenge drawn at another transcript position")
    }
}
impl std::error::Error for StaleChallenge {}

#[cfg(test)]
mod tests;
