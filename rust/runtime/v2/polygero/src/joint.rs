// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Typed recursive participants sharing a column oracle and query set.
use sha2::{Digest as _, Sha256};

#[doc(hidden)]
pub use super::transcript::Challenges as FieldChallenges;
use super::{
    constraints, ensure, transcript, PolygeroCommitment, PolygeroConfig, PolygeroError,
    PolygeroLinearTerm, PolygeroParam,
};
pub use crate::runtime::proto::polygero::{FieldProof, JointPolygeroProof};
#[cfg(any(test, feature = "prover"))]
use crate::runtime::random::RandomEngine;
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{EvaluationDomain, RuntimeField, SupportsSampling},
        proto::Digest,
        random::transcript_v2::{Reading, Transcript, Writing},
    },
};

/// Field and domain references remain typed; parameters own their initialization state.
pub struct Participant<'a, const W: usize, F: RuntimeField<W>, D> {
    pub(super) param: PolygeroParam,
    f: &'a F,
    domain: &'a D,
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
    pub fn new(param: PolygeroParam, f: &'a F, domain: &'a D) -> Result<Self, PolygeroError> {
        ensure(
            param.domain_id == domain.domain_id(),
            "joint interpolation domain mismatch",
        )?;
        param.geom.validate()?;
        ensure(
            f.serialized_size_bytes() > 0,
            "zero joint field encoding width",
        )?;
        Ok(Self { param, f, domain })
    }
}
/// The caller binds the source statement and compiles A*w+b=0 locally.
/// `digest` identifies the public source, such as a circuit ID. Every dynamic
/// input to compilation must already be bound on the same transcript before
/// batching. The verifier reconstructs `a` and `b`; the source binding does not
/// depend on sparse term ordering and needs no separate transcript query.
#[derive(Clone)]
pub struct LinearStatement<E> {
    pub a: Vec<PolygeroLinearTerm<E>>,
    pub b: Vec<E>,
    pub digest: Digest,
}
mod sealed {
    pub trait Sealed {}
    impl Sealed for () {}
    impl<H, T: Sealed> Sealed for (H, T) {}
}

/// Implemented only for () and typed (Participant, Tail) pairs.
/// Separate passes bind every statement before challenges, and every response
/// before queries. Tuple positions preserve field types and participant order.
/// For example, `(hash, (signature, ()))` has matching witness and proof tuples;
/// the fields need not have the same element type or number of witness rows.
pub trait Participants: sealed::Sealed {
    type Witnesses;
    type Statements;
    type States;
    type Bodies;
    type Challenges;
    fn describe(
        &self,
        config: &mut Option<PolygeroConfig>,
        h: &mut Sha256,
    ) -> Result<usize, PolygeroError>;
    fn validate_statements(&self, s: &Self::Statements) -> Result<(), PolygeroError>;
    // Statement digests bind the caller's source; sparse arrays are compiled locally.
    fn bind_statements(&self, s: &Self::Statements, t: &mut Writing<'_>);
    fn challenges(&self, s: &Self::Statements, t: &mut Reading<'_>) -> Self::Challenges;
    fn bind_responses(&self, b: &Self::Bodies, t: &mut Writing<'_>);
    fn validate_bodies(&self, b: &Self::Bodies) -> Result<(), PolygeroError>;
    fn write_bodies(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError>;
    fn read_bodies(&self, bytes: &mut &[u8]) -> Result<Self::Bodies, PolygeroError>;
    #[cfg(any(test, feature = "prover"))]
    fn validate_witnesses(&self, w: &Self::Witnesses) -> Result<(), PolygeroError>;
    #[cfg(any(test, feature = "prover"))]
    fn encode(&self, w: Self::Witnesses, rng: &mut impl RandomEngine) -> Self::States;
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
    type States = ();
    type Bodies = ();
    type Challenges = ();
    fn describe(
        &self,
        _: &mut Option<PolygeroConfig>,
        _: &mut Sha256,
    ) -> Result<usize, PolygeroError> {
        Ok(0)
    }
    fn validate_statements(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    fn bind_statements(&self, _: &(), _: &mut Writing<'_>) {}
    fn challenges(&self, _: &(), _: &mut Reading<'_>) {}
    fn bind_responses(&self, _: &(), _: &mut Writing<'_>) {}
    fn validate_bodies(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    fn write_bodies(&self, _: &(), _: &mut Vec<u8>) -> Result<(), PolygeroError> {
        Ok(())
    }
    fn read_bodies(&self, _: &mut &[u8]) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "prover"))]
    fn validate_witnesses(&self, _: &()) -> Result<(), PolygeroError> {
        Ok(())
    }
    #[cfg(any(test, feature = "prover"))]
    fn encode(&self, _: (), _: &mut impl RandomEngine) {}
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
fn append_values<F: SerializableField>(
    f: &F,
    values: impl IntoIterator<Item = F::E>,
    h: &mut Sha256,
) {
    let mut buf = vec![0; f.serialized_size_bytes()];
    for x in values {
        f.to_bytes_into(&x, &mut buf);
        h.update(&buf);
    }
}
impl<
        const W: usize,
        F: RuntimeField<W> + SerializableField + SupportsSampling,
        D: EvaluationDomain<W, F>,
        T: Participants,
    > Participants for (Participant<'_, W, F, D>, T)
{
    type Witnesses = (Vec<F::E>, T::Witnesses);
    type Statements = (LinearStatement<F::E>, T::Statements);
    type States = (Vec<Vec<F::E>>, T::States);
    type Bodies = (FieldProof<F::E>, T::Bodies);
    type Challenges = (FieldChallenges<F::E>, T::Challenges);
    fn describe(
        &self,
        config: &mut Option<PolygeroConfig>,
        h: &mut Sha256,
    ) -> Result<usize, PolygeroError> {
        let p = &self.0;
        let g = p.param.geom;
        let c = PolygeroConfig {
            k: g.k,
            s: g.s,
            n: g.n,
            t: g.t,
        };
        // One query index addresses a column in every field. The common profile
        // fixes that index range and response sizes; witness row counts may differ.
        ensure(config.is_none_or(|old| old == c), "joint geometry mismatch")?;
        *config = Some(c);
        // The domain identity includes the field representation and point ordering.
        h.update((p.f.serialized_size_bytes() as u64).to_le_bytes());
        h.update(p.param.context.data);
        Ok(1 + self.1.describe(config, h)?)
    }
    fn validate_statements(&self, s: &Self::Statements) -> Result<(), PolygeroError> {
        constraints::validate(self.0.param.geom.nw, s.0.b.len(), &s.0.a)?;
        self.1.validate_statements(&s.1)
    }
    fn bind_statements(&self, s: &Self::Statements, t: &mut Writing<'_>) {
        transcript::bind_statement(t, &s.0.digest, &self.0.param.context, s.0.b.len());
        self.1.bind_statements(&s.1, t);
    }
    fn challenges(&self, s: &Self::Statements, t: &mut Reading<'_>) -> Self::Challenges {
        (
            transcript::challenges(t, &self.0.param, s.0.b.len(), self.0.f),
            self.1.challenges(&s.1, t),
        )
    }
    fn bind_responses(&self, b: &Self::Bodies, t: &mut Writing<'_>) {
        transcript::bind_response(t, &b.0, self.0.f);
        self.1.bind_responses(&b.1, t);
    }
    fn validate_bodies(&self, b: &Self::Bodies) -> Result<(), PolygeroError> {
        b.0.validate(&self.0.param.geom)?;
        self.1.validate_bodies(&b.1)
    }
    fn write_bodies(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError> {
        b.0.write(out, &self.0.param.geom, self.0.f)?;
        self.1.write_bodies(&b.1, out)
    }
    fn read_bodies(&self, bytes: &mut &[u8]) -> Result<Self::Bodies, PolygeroError> {
        Ok((
            FieldProof::read(bytes, &self.0.param.geom, self.0.f)?,
            self.1.read_bodies(bytes)?,
        ))
    }
    #[cfg(any(test, feature = "prover"))]
    fn validate_witnesses(&self, w: &Self::Witnesses) -> Result<(), PolygeroError> {
        ensure(w.0.len() == self.0.param.geom.nw, "witness length mismatch")?;
        self.1.validate_witnesses(&w.1)
    }
    #[cfg(any(test, feature = "prover"))]
    fn encode(&self, w: Self::Witnesses, rng: &mut impl RandomEngine) -> Self::States {
        (
            super::prover_commitment::encode_rows(&self.0.param, w.0, self.0.domain, rng, self.0.f),
            self.1.encode(w.1, rng),
        )
    }
    #[cfg(any(test, feature = "prover"))]
    fn append_encoded(&self, w: &Self::States, j: usize, h: &mut Sha256) {
        // A leaf concatenates column j from every participant in tuple order.
        // The context fixes field widths and row counts, so no separators are needed.
        append_values(self.0.f, w.0.iter().map(|row| row[j].clone()), h);
        self.1.append_encoded(&w.1, j, h);
    }
    #[cfg(any(test, feature = "prover"))]
    fn respond(
        &self,
        w: &Self::States,
        s: &Self::Statements,
        c: &Self::Challenges,
    ) -> Self::Bodies {
        (
            super::prover::respond(&self.0.param, &w.0, &s.0, &c.0, self.0.domain, self.0.f),
            self.1.respond(&w.1, &s.1, &c.1),
        )
    }
    #[cfg(any(test, feature = "prover"))]
    fn gather(&self, w: &Self::States, b: &mut Self::Bodies, indices: &[usize]) {
        super::prover::gather(&w.0, &mut b.0, indices);
        self.1.gather(&w.1, &mut b.1, indices);
    }
    #[cfg(any(test, feature = "verifier"))]
    fn append_opened(&self, w: &Self::Bodies, q: usize, t: usize, h: &mut Sha256) {
        // Proof rows store t values in query order. Here q is the position in
        // that order, whereas append_encoded receives the actual column index.
        append_values(
            self.0.f,
            w.0.rows.chunks_exact(t).map(|row| row[q].clone()),
            h,
        );
        self.1.append_opened(&w.1, q, t, h);
    }
    #[cfg(any(test, feature = "verifier"))]
    fn check(
        &self,
        b: &Self::Bodies,
        s: &Self::Statements,
        c: &Self::Challenges,
        indices: &[usize],
    ) -> Result<(), PolygeroError> {
        super::verifier::check_response(
            &self.0.param,
            &b.0,
            &s.0,
            &c.0,
            indices,
            self.0.domain,
            self.0.f,
        )?;
        self.1.check(&b.1, &s.1, &c.1, indices)
    }
}
/// Immutable validated geometry, ordered participants and joint hash identity.
#[derive(Clone)]
pub struct JointPolygeroParam<L: Participants> {
    pub(super) participants: L,
    pub(super) config: PolygeroConfig,
    pub(super) context: Digest,
}
impl<L: Participants> JointPolygeroParam<L> {
    pub fn new(participants: L) -> Result<Self, PolygeroError> {
        let mut h = Sha256::new();
        h.update(b"polygero/joint/context/v1");
        let mut config = None;
        let count = participants.describe(&mut config, &mut h)?;
        ensure(count > 0, "empty joint participant list")?;
        h.update((count as u64).to_le_bytes());
        Ok(Self {
            participants,
            config: config.unwrap(),
            context: Digest {
                data: h.finalize().into(),
            },
        })
    }
    pub fn context(&self) -> Digest {
        self.context
    }
    pub fn config(&self) -> PolygeroConfig {
        self.config
    }
    pub fn commitment_context(&self) -> JointCommitmentContext {
        JointCommitmentContext {
            context: self.context,
        }
    }
    pub fn write(
        &self,
        p: &JointPolygeroProof<L::Bodies>,
        transcript: Transcript,
    ) -> Result<crate::runtime::random::transcript_v2::EncodedProof, PolygeroError> {
        let mut out = Vec::new();
        p.write_to_buf(
            &mut out,
            &self.context,
            self.config.t,
            self.config.n,
            |b, out| self.participants.write_bodies(b, out),
        )?;
        Ok(transcript.append_final_seal(out))
    }
    pub fn read<'a>(
        &self,
        bytes: &mut &'a [u8],
    ) -> Result<
        crate::runtime::random::transcript_v2::Unverified<'a, JointPolygeroProof<L::Bodies>>,
        PolygeroError,
    > {
        let input = *bytes;
        let body = JointPolygeroProof::read(
            bytes,
            &self.context,
            self.config.t,
            self.config.n,
            |bytes| self.participants.read_bodies(bytes),
        )?;
        crate::runtime::random::transcript_v2::Unverified::decoded(body, input, bytes)
            .map_err(Into::into)
    }
}
/// An owned context lets callers receive the root before constructing the
/// field/domain borrows used for the later arithmetic verification.
#[derive(Clone)]
pub struct JointCommitmentContext {
    pub(super) context: Digest,
}
/// Records the context and root already absorbed into the caller's transcript.
/// Reattaching the arithmetic parameters must not absorb the root a second time.
/// The caller must continue the same transcript; this token does not own it.
#[derive(Clone)]
pub struct ReceivedCommitment {
    pub(super) _context: Digest,
    pub(super) _root: PolygeroCommitment,
}
#[cfg(test)]
#[path = "../tests/joint.rs"]
mod tests;
