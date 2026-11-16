// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Typed recursive participants sharing a column oracle and query set.
use sha2::Sha256;

use super::{ensure, PolygeroError, PolygeroLinearTerm, PolygeroParam};
#[cfg(any(test, feature = "prover"))]
use crate::runtime::random::PrivateRandom;
#[cfg(any(test, feature = "testonly"))]
use crate::runtime::v2::transcript::{EncodedProof, Transcript};
#[cfg(any(test, feature = "testonly", feature = "tooling"))]
use crate::runtime::v2::{
    proto::polygero::{checked_body, JointPolygeroProof},
    transcript::{Unverified, SEAL_BYTES},
};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{range_interpolation::EvaluationDomain, RuntimeField, SupportsSampling},
        v2::{
            proto::polygero::PolygeroConfig,
            transcript::{Reading, SessionStamp, TranscriptRef},
        },
    },
};

/// Widest field encoding a joint participant accepts. Every supported field
/// is far narrower; the bound keeps codec and proof-size arithmetic small.
pub(crate) const MAX_FIELD_BYTES: usize = 128;

/// Field and domain references remain typed; parameters own their initialization state.
pub struct Participant<'a, const W: usize, F: RuntimeField<W>, D> {
    pub(super) param: PolygeroParam,
    pub(super) f: &'a F,
    pub(super) domain: &'a D,
}
impl<const W: usize, F: RuntimeField<W>, D> Clone for Participant<'_, W, F, D> {
    fn clone(&self) -> Self {
        Self {
            param: self.param.clone(),
            f: self.f,
            domain: self.domain,
        }
    }
}
impl<
        'a,
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
        D: EvaluationDomain<W, F>,
    > Participant<'a, W, F, D>
{
    pub fn new(param: PolygeroParam, domain: &'a D) -> Result<Self, PolygeroError> {
        let f = domain.field();
        ensure(
            param.domain_id == domain.domain_id(),
            "joint interpolation domain mismatch",
        )?;
        param.geom.validate()?;
        let g = param.geom;
        // Identity fixes the field and point order, not the implementation's
        // capacity. Reattaching to another backend must validate its ranges.
        ensure(
            PolygeroConfig {
                k: g.k,
                s: g.s,
                n: g.n,
                t: g.t,
            }
            .can_interpolate(domain),
            "interpolation capacity exceeded",
        )?;
        ensure(
            (1..=MAX_FIELD_BYTES).contains(&f.serialized_size_bytes()),
            "unsupported joint field encoding width",
        )?;
        Ok(Self { param, f, domain })
    }
}
/// An immutable affine statement `A*w+b=0`: one field's equations. A
/// frontend derives them from messages and challenges already absorbed,
/// which fixes them before the batching weights; they are never absorbed
/// (transcript I3). They carry the stamp of the session that derived them,
/// and the joint opening of a complete proof (`zk::JointProver::finish`,
/// `zk::JointVerifier::finish`) accepts only equations derived on its own
/// session. Only frontends inside the crate build them:
///
/// ```compile_fail,E0451
/// use longfellow_zk::runtime::v2::{polygero::LinearStatement, transcript::SessionStamp};
/// fn forge(session: SessionStamp) -> LinearStatement<u64> {
///     LinearStatement { a: vec![], b: vec![], session }
/// }
/// ```
///
/// Tests and tools may build a static system with [`Self::new`], which the
/// transcript does not bind.
#[derive(Clone)]
#[must_use = "The derived statement must be authenticated by the commitment backend."]
pub struct LinearStatement<E> {
    pub(crate) a: Vec<PolygeroLinearTerm<E>>,
    pub(crate) b: Vec<E>,
    /// The session the equations were derived on.
    pub(crate) session: SessionStamp,
}
impl<E> LinearStatement<E> {
    /// A static system `A*w+b=0`, for tests and tools only. The transcript
    /// does not bind it: nothing absorbs a statement, so a static system is
    /// sound only if the caller fixes it in the transcript statement (for
    /// example in the context) before the commitment. It belongs to no
    /// session, so a complete proof's joint opening rejects it; the bare
    /// joint prover and verifier accept it. Frontend-derived systems are
    /// constructed internally.
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    pub fn new(a: Vec<PolygeroLinearTerm<E>>, b: Vec<E>) -> Self {
        Self {
            a,
            b,
            session: SessionStamp::detached(),
        }
    }
}
/// Independent constraint-batching scalars and evaluation-basis polynomial samples.
#[doc(hidden)]
pub struct FieldChallenges<E> {
    /// One independent weight per affine equation.
    pub(super) alpha: Vec<E>,
    /// Uniform evaluations of B_i on the first s+1 nodes of the oracle.
    /// Entry i belongs to W_i; the final row fstar has no batching polynomial.
    pub(super) batching_samples: Vec<Vec<E>>,
}
mod sealed {
    pub trait Sealed {}
    impl Sealed for () {}
    impl<H, T: Sealed> Sealed for (H, T) {}
}

/// Implemented only for () and typed (Participant, Tail) pairs.
/// Separate passes draw every field's challenges, then send every response
/// before the queries. Tuple positions preserve field types and participant order.
/// For example, `(hash, (signature, ()))` has matching witness and proof tuples;
/// the fields need not have the same element type or number of witness rows.
pub trait Participants: sealed::Sealed {
    type Witnesses;
    type Statements;
    /// The prover's encoded rows between commitment and opening.
    #[cfg(any(test, feature = "prover"))]
    type States;
    type Bodies;
    type Challenges;
    /// Check that every participant has one profile, written to `config`;
    /// return the participant count.
    fn describe(&self, config: &mut Option<PolygeroConfig>) -> Result<usize, PolygeroError>;
    fn validate_statements(&self, s: &Self::Statements) -> Result<(), PolygeroError>;
    /// Draw every field's challenges for the equations of `s`: one weight
    /// per equation, then s+1 samples per batched row.
    fn challenges(&self, s: &Self::Statements, t: &mut Reading<'_>) -> Self::Challenges;
    fn send_responses(&self, b: &Self::Bodies, t: &mut TranscriptRef<'_>);
    fn validate_bodies(&self, b: &Self::Bodies) -> Result<(), PolygeroError>;
    // The bare body codec of `JointPolygeroParam::{write, read}`, for tests
    // and tools only. Complete proofs encode the field bodies themselves.
    /// Bytes of every field's response and rows; None if they overflow.
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn wire_len(&self) -> Option<usize>;
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn write_responses(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError>;
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn write_rows(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError>;
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn read_responses(&self, bytes: &mut &[u8]) -> Result<Self::Bodies, PolygeroError>;
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn read_rows(&self, b: &mut Self::Bodies, bytes: &mut &[u8]) -> Result<(), PolygeroError>;
    #[cfg(any(test, feature = "prover"))]
    fn validate_witnesses(&self, w: &Self::Witnesses) -> Result<(), PolygeroError>;
    /// Check that every field's rows were encoded for this list's geometry.
    #[cfg(any(test, feature = "prover"))]
    fn validate_states(&self, w: &Self::States) -> Result<(), PolygeroError>;
    #[cfg(any(test, feature = "prover"))]
    fn encode(&self, w: Self::Witnesses, rng: &mut impl PrivateRandom) -> Self::States;
    #[cfg(any(test, feature = "prover"))]
    fn append_encoded(&self, w: &Self::States, j: usize, h: &mut Sha256);
    #[cfg(any(test, feature = "prover"))]
    fn respond(&self, w: &Self::States, s: &Self::Statements, c: &Self::Challenges)
        -> Self::Bodies;
    #[cfg(any(test, feature = "prover"))]
    fn gather(&self, w: &Self::States, b: &mut Self::Bodies, indices: &[usize]);
    #[cfg(any(test, feature = "verifier"))]
    fn append_opened(&self, w: &Self::Bodies, q: usize, t: usize, h: &mut Sha256);
    #[cfg(any(test, feature = "verifier"))]
    fn check(
        &self,
        b: &Self::Bodies,
        s: &Self::Statements,
        c: &Self::Challenges,
        indices: &[usize],
    ) -> Result<(), PolygeroError>;
}
impl Participants for () {
    type Witnesses = ();
    type Statements = ();
    #[cfg(any(test, feature = "prover"))]
    type States = ();
    type Bodies = ();
    type Challenges = ();
    fn describe(&self, _: &mut Option<PolygeroConfig>) -> Result<usize, PolygeroError> {
        Ok(0)
    }
    fn validate_statements(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    fn challenges(&self, _: &(), _: &mut Reading<'_>) {}
    fn send_responses(&self, _: &(), _: &mut TranscriptRef<'_>) {}
    fn validate_bodies(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn wire_len(&self) -> Option<usize> {
        Some(0)
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn write_responses(&self, _: &(), _: &mut Vec<u8>) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn write_rows(&self, _: &(), _: &mut Vec<u8>) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn read_responses(&self, _: &mut &[u8]) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    fn read_rows(&self, _: &mut (), _: &mut &[u8]) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "prover"))]
    fn validate_witnesses(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "prover"))]
    fn validate_states(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "prover"))]
    fn encode(&self, _: (), _: &mut impl PrivateRandom) {}
    #[cfg(any(test, feature = "prover"))]
    fn append_encoded(&self, _: &(), _: usize, _: &mut Sha256) {}
    #[cfg(any(test, feature = "prover"))]
    fn respond(&self, _: &(), _: &(), _: &()) {}
    #[cfg(any(test, feature = "prover"))]
    fn gather(&self, _: &(), _: &mut (), _: &[usize]) {}
    #[cfg(any(test, feature = "verifier"))]
    fn append_opened(&self, _: &(), _: usize, _: usize, _: &mut Sha256) {}
    #[cfg(any(test, feature = "verifier"))]
    fn check(&self, _: &(), _: &(), _: &(), _: &[usize]) -> Result<(), PolygeroError> {
        Ok(())
    }
}
/// Immutable validated geometry and ordered participants. Their profile and
/// cell counts are bound by the transcript statement; the column tree hashes
/// under the fixed Merkle hash domain.
#[derive(Clone)]
pub struct JointPolygeroParam<L: Participants> {
    pub(super) participants: L,
    pub(super) config: PolygeroConfig,
}
impl<L: Participants> JointPolygeroParam<L> {
    pub fn new(participants: L) -> Result<Self, PolygeroError> {
        let mut config = None;
        let count = participants.describe(&mut config)?;
        ensure(count > 0, "empty joint participant list")?;
        Ok(Self {
            participants,
            config: config.unwrap(),
        })
    }
    pub fn config(&self) -> PolygeroConfig {
        self.config
    }
    /// A sealed bare body, for tests and tools only: each field's response,
    /// each field's rows, the nonces and the frontier, then the seal block.
    /// It has no magic. Complete proofs embed the joint body in their own
    /// envelope (`runtime::v2::proto::zk`, `mdoc`).
    #[cfg(any(test, feature = "testonly"))]
    pub fn write(
        &self,
        p: &JointPolygeroProof<L::Bodies>,
        transcript: Transcript,
    ) -> Result<EncodedProof, PolygeroError> {
        let mut out = Vec::new();
        p.write_to_buf(
            &mut out,
            self.config.t,
            self.config.n,
            |b, buf| self.participants.write_responses(b, buf),
            |b, buf| self.participants.write_rows(b, buf),
        )?;
        Ok(transcript.append_final_seal(out))
    }
    /// Read a sealed bare body, for tests and tools only; its length is
    /// checked first (proto I3).
    #[cfg(any(test, feature = "testonly", feature = "tooling"))]
    pub fn read<'a>(
        &self,
        bytes: &mut &'a [u8],
    ) -> Result<Unverified<'a, JointPolygeroProof<L::Bodies>>, PolygeroError> {
        let input = *bytes;
        let (t, n) = (self.config.t, self.config.n);
        let fixed = self
            .participants
            .wire_len()
            .zip(JointPolygeroProof::<()>::fixed_opening_len(t))
            .and_then(|(a, b)| a.checked_add(b))
            .ok_or(PolygeroError("joint proof size overflow".into()))?;
        let mut body = checked_body(input, 0, fixed, t, n)?;
        let proof = JointPolygeroProof::read(
            &mut body,
            t,
            n,
            |rest| self.participants.read_responses(rest),
            |bodies, rest| self.participants.read_rows(bodies, rest),
        )?;
        let mut seal = &input[input.len() - SEAL_BYTES..];
        *bytes = &[];
        Unverified::decoded(proof, input, &mut seal).map_err(Into::into)
    }
}

#[cfg(test)]
mod tests;
