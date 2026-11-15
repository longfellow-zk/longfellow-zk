// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The mdoc statement, shared by the proof roles (transcript I1).
//!
//! An mdoc transcript opens with `MdocStatement` (protocol ID, session
//! transcript, spec), then the composition's statement messages: the hash
//! circuit, adapter fragment and signature circuit, both fields'
//! commitment layouts, the adapter layout, the joint geometry, and the
//! public inputs of the hash circuit (as GF(2^128) elements) and of the
//! signature circuit (as P-256 elements).
use super::{link::Statement as Composed, proto::MdocProofGeometry, ZkSpecStruct};
use crate::runtime::{
    algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
    v2::{
        proto::tags::Tag,
        transcript::{Encoder, Header, Message, SetupMessage, Statement},
    },
};

/// The protocol ID of `MdocStatement`.
pub(super) const PROTOCOL_ID: &[u8] = b"longfellow/v2/mdoc/transcript/v2";

/// `MdocStatement` (16): Bytes protocol ID (`PROTOCOL_ID`); Bytes session
/// transcript; Bytes(32) the spec's combined archive hash; Nats(circuit
/// version, attribute count). The Polygero profile is in `JointGeometry`.
struct Identity<'a> {
    session: &'a [u8],
    spec: &'a ZkSpecStruct,
}
impl Message for Identity<'_> {
    const TAG: Tag = Tag::MdocStatement;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(PROTOCOL_ID);
        e.bytes(self.session);
        e.bytes(&self.spec.combined_hash);
        e.nats(&[self.spec.version as u64, self.spec.num_attributes as u64]);
    }
}
impl SetupMessage for Identity<'_> {}

/// Everything an mdoc verifier fixes before it reads a proof byte.
pub(super) struct MdocStatement<'s, DH, DS>
where
    DH: EvaluationDomain<2, Gf2_128Field>,
    DS: EvaluationDomain<4, P256Field>,
{
    session: &'s [u8],
    spec: &'s ZkSpecStruct,
    composed: Composed<'s, DH, DS>,
    /// The geometry the statement writes; the proof is parsed against it.
    pub(super) geometry: MdocProofGeometry,
}
impl<'s, DH, DS> MdocStatement<'s, DH, DS>
where
    DH: EvaluationDomain<2, Gf2_128Field>,
    DS: EvaluationDomain<4, P256Field>,
{
    pub(super) fn new(
        session: &'s [u8],
        spec: &'s ZkSpecStruct,
        composed: Composed<'s, DH, DS>,
    ) -> Self {
        let geometry = MdocProofGeometry {
            body: composed.geometry().clone(),
        };
        Self {
            session,
            spec,
            composed,
            geometry,
        }
    }
}
/// The composition part proving and verifying read.
impl<'s, DH, DS> AsRef<Composed<'s, DH, DS>> for MdocStatement<'s, DH, DS>
where
    DH: EvaluationDomain<2, Gf2_128Field>,
    DS: EvaluationDomain<4, P256Field>,
{
    fn as_ref(&self) -> &Composed<'s, DH, DS> {
        &self.composed
    }
}
impl<DH, DS> Statement for MdocStatement<'_, DH, DS>
where
    DH: EvaluationDomain<2, Gf2_128Field>,
    DS: EvaluationDomain<4, P256Field>,
{
    fn write(&self, h: &mut Header<'_>) {
        h.send(&Identity {
            session: self.session,
            spec: self.spec,
        });
        self.composed.write(h);
    }
}

#[cfg(test)]
mod tests;
