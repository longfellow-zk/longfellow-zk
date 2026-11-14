// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Typed recursive participants sharing a column oracle and query set.
use sha2::{Digest as _, Sha256};

#[doc(hidden)]
pub use super::transcript::Challenges as FieldChallenges;
use super::{ensure, PolygeroConfig, PolygeroError, PolygeroLinearTerm, PolygeroParam};
#[cfg(any(test, feature = "prover"))]
use crate::runtime::random::PrivateRandom;
pub use crate::runtime::v2::proto::polygero::{FieldProof, JointPolygeroProof};
use crate::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{EvaluationDomain, RuntimeField, SupportsSampling},
        v2::{
            proto::Digest,
            transcript::{Reading, Transcript, Writing},
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
/// An immutable affine statement. Standalone callers use [`Self::new`], which
/// hashes the complete static statement. Internal frontends instead derive
/// equations from their already absorbed source messages and challenges.
///
/// ```compile_fail
/// use longfellow_zk::runtime::v2::{polygero::LinearStatement, proto::Digest};
/// let statement: LinearStatement<u64> = LinearStatement {
///     a: vec![], b: vec![], digest: Digest { data: [0; 32] },
/// };
/// ```
#[derive(Clone)]
#[must_use = "The derived statement must be authenticated by the commitment backend."]
pub struct LinearStatement<E> {
    pub(crate) a: Vec<PolygeroLinearTerm<E>>,
    pub(crate) b: Vec<E>,
    pub(crate) digest: Digest,
}
impl<E> LinearStatement<E> {
    /// Fix a standalone static system `A*w+b=0`, including every coefficient
    /// and target. Term order is part of this source encoding. Use before any
    /// proof challenges; frontend-derived systems are constructed internally.
    pub fn new<F: SerializableField<E = E>>(
        a: Vec<PolygeroLinearTerm<E>>,
        b: Vec<E>,
        f: &F,
    ) -> Self {
        let mut hash = Sha256::new();
        hash.update(b"polygero/static-linear-statement/v1");
        hash.update([u8::from(f.is_binary())]);
        hash.update((f.serialized_size_bytes() as u64).to_le_bytes());
        hash.update(f.serialized_mone());
        hash.update((b.len() as u64).to_le_bytes());
        hash.update((a.len() as u64).to_le_bytes());
        let mut bytes = vec![0; f.serialized_size_bytes()];
        for term in &a {
            hash.update((term.c as u64).to_le_bytes());
            hash.update((term.w as u64).to_le_bytes());
            f.to_bytes_into(&term.k, &mut bytes);
            hash.update(&bytes);
        }
        for target in &b {
            f.to_bytes_into(target, &mut bytes);
            hash.update(&bytes);
        }
        Self {
            a,
            b,
            digest: Digest {
                data: hash.finalize().into(),
            },
        }
    }
    pub fn terms(&self) -> &[PolygeroLinearTerm<E>] {
        &self.a
    }
    pub fn targets(&self) -> &[E] {
        &self.b
    }
    pub fn digest(&self) -> Digest {
        self.digest
    }
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
    fn absorb_statements(&self, s: &Self::Statements, t: &mut Writing<'_>);
    fn challenges(&self, s: &Self::Statements, t: &mut Reading<'_>) -> Self::Challenges;
    fn absorb_responses(&self, b: &Self::Bodies, t: &mut Writing<'_>);
    fn validate_bodies(&self, b: &Self::Bodies) -> Result<(), PolygeroError>;
    fn write_bodies(&self, b: &Self::Bodies, out: &mut Vec<u8>) -> Result<(), PolygeroError>;
    fn read_bodies(&self, bytes: &mut &[u8]) -> Result<Self::Bodies, PolygeroError>;
    #[cfg(any(test, feature = "prover"))]
    fn validate_witnesses(&self, w: &Self::Witnesses) -> Result<(), PolygeroError>;
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
    fn absorb_statements(&self, _: &(), _: &mut Writing<'_>) {}
    fn challenges(&self, _: &(), _: &mut Reading<'_>) {}
    fn absorb_responses(&self, _: &(), _: &mut Writing<'_>) {}
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
    pub fn write(
        &self,
        p: &JointPolygeroProof<L::Bodies>,
        transcript: Transcript,
    ) -> Result<crate::runtime::v2::transcript::EncodedProof, PolygeroError> {
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
        crate::runtime::v2::transcript::Unverified<'a, JointPolygeroProof<L::Bodies>>,
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
        crate::runtime::v2::transcript::Unverified::decoded(body, input, bytes).map_err(Into::into)
    }
}
#[cfg(test)]
#[path = "../tests/participant.rs"]
mod participant_tests;
#[cfg(test)]
#[path = "../tests/joint.rs"]
mod tests;
