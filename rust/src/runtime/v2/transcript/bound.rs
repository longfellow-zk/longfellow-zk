// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Statement-bound transcript capabilities and stamped challenges.
//!
//! A `Bound` pairs a session with the statement part a component reads, so
//! the component uses the values its caller holds next to the transcript
//! (transcript I2). Outside the crate a `Bound` comes only from a named
//! accessor of an `Opened` session, which binds a part of the statement the
//! session opened with; binding an arbitrary value is crate-private. A
//! `Challenge` is a value drawn at one boundary of one session for the next
//! component. Its consumer accepts it only on that session while it still
//! stands at that boundary, with no message sent since (transcript I8).
use super::session::{Position, Reading, SessionStamp, Statement, Transcript, TranscriptRef};

impl Transcript {
    /// Bind `part`, the statement part a component reads, to this session.
    /// The caller is responsible for `part` being a part of the statement
    /// this session opened with.
    pub(crate) fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P> {
        Bound { part, owner: self }
    }
    /// Bind any `part` to this session, for tests and benchmarks outside the
    /// crate that run a component on a bare session (`for_test`). Nothing
    /// ties `part` to the statement.
    #[cfg(feature = "testonly")]
    pub fn bound_for_test<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P> {
        self.bound(part)
    }
}

/// A session together with the statement it was opened with. Proving and
/// verifying entry points take one and read every part from its statement,
/// so a transcript opened with one statement cannot be used to check another
/// (transcript I1, I2).
pub struct Opened<'s, S: ?Sized> {
    statement: &'s S,
    transcript: Transcript,
}
impl<'s, S: Statement + ?Sized> Opened<'s, S> {
    /// Open a session with `statement` (`Transcript::new`).
    pub fn new(statement: &'s S) -> Self {
        Self {
            statement,
            transcript: Transcript::new(statement),
        }
    }
}
impl<'s, S: ?Sized> Opened<'s, S> {
    /// The statement this session opened with.
    pub fn statement(&self) -> &'s S {
        self.statement
    }
    /// The session, bound to a part of its own statement; for example the
    /// geometry a proof reader parses against. Statement types expose this
    /// through named accessors; `f` must return a part of its argument.
    pub(crate) fn bound<P: ?Sized + 's>(&mut self, f: impl FnOnce(&'s S) -> &'s P) -> Bound<'_, P> {
        let part = f(self.statement);
        self.transcript.bound(part)
    }
    /// The statement and the session, for the drivers that own the session
    /// from here on.
    pub(crate) fn into_parts(self) -> (&'s S, Transcript) {
        (self.statement, self.transcript)
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
    /// The same session, bound to a part of this part; `f` must return a
    /// part of its argument.
    pub(crate) fn project<Q: ?Sized + 'a>(
        &mut self,
        f: impl FnOnce(&'a P) -> &'a Q,
    ) -> Bound<'_, Q> {
        Bound {
            part: f(self.part),
            owner: self.owner,
        }
    }
    /// The session's identity, for states that span several calls.
    pub fn session(&self) -> SessionStamp {
        self.owner.session()
    }
    /// Consume `c` if it was drawn on this session and the session still
    /// stands where it was drawn.
    pub fn accept<T>(&self, c: Challenge<T>) -> Result<T, StaleChallenge> {
        c.accept(self.owner)
    }
    /// The session's message and round operations.
    pub(crate) fn transcript(&mut self) -> TranscriptRef<'_> {
        self.owner.borrow()
    }
    /// Draw a value a later component consumes.
    pub(crate) fn challenge<T>(&mut self, f: impl FnOnce(&mut Reading<'_>) -> T) -> Challenge<T> {
        self.transcript().challenge(f)
    }
}
impl TranscriptRef<'_> {
    /// Draw a value a later component consumes, stamped with the boundary
    /// it reads from (transcript I7, I8).
    pub(crate) fn challenge<T>(&mut self, f: impl FnOnce(&mut Reading<'_>) -> T) -> Challenge<T> {
        let value = self.draw(f);
        Challenge {
            value,
            at: self.session.position(),
            session: self.session.session(),
        }
    }
    /// Consume `c` if it was drawn on this session and the session still
    /// stands where it was drawn.
    pub(crate) fn accept<T>(&self, c: Challenge<T>) -> Result<T, StaleChallenge> {
        c.accept(self.session)
    }
}

#[doc = include_str!("bound_compile_fail.md")]
/// A value drawn from a transcript, stamped with the session and the
/// boundary it came from: the session's identity, the node index, a private
/// copy of that node's digest, and the session's message count. Two sessions
/// with equal histories have equal positions, so the identity is what tells
/// them apart. It is not `Clone`, and accepting it consumes it.
#[must_use = "a challenge is drawn for a consumer that must accept it"]
pub struct Challenge<T> {
    value: T,
    at: Position,
    session: SessionStamp,
}
impl<T> Challenge<T> {
    fn accept(self, now: &Transcript) -> Result<T, StaleChallenge> {
        if now.is_session(&self.session) && self.at == now.position() {
            Ok(self.value)
        } else {
            Err(StaleChallenge)
        }
    }
    /// The same draw, still stamped with its boundary, with its value
    /// replaced by `f(value)`: for a component that derives its consumer's
    /// input from the drawn value and values fixed before the draw. Witness
    /// selection attaches its fingerprint equations to the batched system
    /// this way.
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn try_map<U, E>(
        self,
        f: impl FnOnce(T) -> Result<U, E>,
    ) -> Result<Challenge<U>, E> {
        Ok(Challenge {
            value: f(self.value)?,
            at: self.at,
            session: self.session,
        })
    }
}

/// A challenge was drawn on another session or at another boundary, or a
/// message was sent after it was drawn.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StaleChallenge;
impl std::fmt::Display for StaleChallenge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("challenge drawn on another session or at another position")
    }
}
impl std::error::Error for StaleChallenge {}

#[cfg(test)]
mod tests;
