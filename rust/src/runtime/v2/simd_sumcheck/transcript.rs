// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Typed SIMD messages and the immutable packed-source statement.
use super::*;
use crate::{
    runtime::v2::{
        proto::{polygero::PolygeroConfig, tags::Tag},
        transcript::{
            Encoder, Header, Message, ProverMessage, SetupMessage, Statement, Transcript,
        },
        zk::write_joint_geometry,
    },
    util::ceil_log2,
};
macro_rules! message {
    ($name:ident, $tag:ident) => {
        struct $name<'a>(&'a [E], &'a F);
        impl Message for $name<'_> {
            const TAG: Tag = Tag::$tag;
            fn encode(&self, e: &mut Encoder<'_>) {
                e.elements(self.1, self.0);
            }
        }
        impl ProverMessage for $name<'_> {}
    };
}
message!(Round, SumcheckRound);
message!(Cross, SumcheckCross);
message!(Claims, SumcheckClaims);
message!(Nonlinear, SimdNonlinear);
pub(super) fn round(m: &RoundPoly<F>, t: &mut TranscriptRef<'_>, f: &F) -> E {
    t.send(&Round(&m.coefficients, f));
    t.draw(|r| r.elt_field(f))
}
pub(super) fn terminal(cross: &E, t: &mut TranscriptRef<'_>, f: &F) -> E {
    t.send(&Cross(std::slice::from_ref(cross), f));
    t.draw(|r| r.nonzero(f))
}
pub(super) fn combine(claims: &[E; 2], t: &mut TranscriptRef<'_>, f: &F) -> E {
    t.send(&Claims(claims, f));
    t.draw(|r| r.elt_field(f))
}
pub(super) fn nonlinear(message: E, t: &mut TranscriptRef<'_>, f: &F) {
    t.send(&Nonlinear(std::slice::from_ref(&message), f));
}
struct Identity<'a>(&'a [u8]);
impl Message for Identity<'_> {
    const TAG: Tag = Tag::SimdStatement;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(b"longfellow/simd/packed-PCS/v3");
        e.bytes(self.0);
    }
}
impl SetupMessage for Identity<'_> {}
struct Layout<'a>(&'a Program);
impl Message for Layout<'_> {
    const TAG: Tag = Tag::SimdLayout;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(&self.0.id);
        e.nats(&[self.0.real as u64, self.0.cell_count() as u64]);
    }
}
impl SetupMessage for Layout<'_> {}
struct Standalone<'a> {
    identity: Identity<'a>,
    program: &'a Program,
    config: PolygeroConfig,
}
impl<'a> Statement for Standalone<'a> {
    type Identity = Identity<'a>;
    fn identity(&self) -> &Self::Identity {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        self.program.write_layout(h);
        write_joint_geometry(h, self.config);
    }
}
impl Program {
    pub(super) fn start(&self, context: &[u8], config: PolygeroConfig) -> Transcript {
        Transcript::new(&Standalone {
            identity: Identity(context),
            program: self,
            config,
        })
    }
    pub(crate) fn write_layout(&self, h: &mut Header<'_>) {
        h.send(&Layout(self));
    }
    /// Protocol entries draw leading weights at the preceding message's boundary.
    pub(super) fn top_weights(&self, t: &mut TranscriptRef<'_>) -> Vec<E> {
        t.draw(|r| {
            let point: Vec<_> = r
                .elements(self.packing.field(), ceil_log2(self.circuit.raw.noutput))
                .collect();
            super::program::monomials(&point, self.circuit.raw.noutput)
        })
    }
}
#[cfg(feature = "mldsa")]
pub(super) fn scalar_mix(t: &mut TranscriptRef<'_>, f: &F) -> E {
    t.draw(|r| r.elt_field(f))
}
pub(super) fn mapped_linear_mix(t: &mut TranscriptRef<'_>, f: &F) -> E {
    t.draw(|r| r.elt_field(f))
}
