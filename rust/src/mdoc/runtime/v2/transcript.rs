// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The mdoc statement, shared by the proof roles (transcript I1).
//!
//! An mdoc transcript opens with `MdocStatement` (protocol ID, session
//! transcript, spec), then the composition's statement messages: the hash
//! circuit, adapter fragment and signature circuit, both fields'
//! commitment layouts, the adapter layout, the joint geometry, and the
//! public inputs of the hash circuit (as GF(2^128) elements) and of the
//! signature circuit (as P-256 elements).
use super::{
    inputs::PublicInputs,
    link::{Composition, Statement as Composed},
    request::Request,
    ZkSpecStruct,
};
use crate::runtime::{
    algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
    v2::{
        proto::tags::Tag,
        transcript::{Encoder, Message, SetupMessage},
    },
};

/// The protocol ID of `MdocStatement`.
pub(super) const PROTOCOL_ID: &[u8] = b"longfellow/v2/mdoc/transcript/v2";

/// `MdocStatement` (16): Bytes protocol ID (`PROTOCOL_ID`); Bytes session
/// transcript; Bytes(32) the spec's combined archive hash; Nats(circuit
/// version, attribute count). The Polygero profile is in `JointGeometry`.
/// Built only from a checked `Request` (`statement`).
pub(super) struct Identity<'a> {
    session: &'a [u8],
    spec: &'a ZkSpecStruct,
}
impl<'a> Identity<'a> {
    /// The identity of a checked request: its session transcript and spec.
    fn of(request: &Request<'a>) -> Self {
        Self {
            session: request.transcript(),
            spec: request.spec(),
        }
    }
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

/// Everything an mdoc verifier fixes before it reads a proof byte: the
/// composition's statement under the mdoc identity. The proof is parsed
/// against the geometry it writes (`Opened::geometry`).
pub(super) type MdocStatement<'s, DH, DS> = Composed<'s, DH, DS, Identity<'s>>;

/// The statement of a checked request on the public inputs derived from it
/// (`PublicInputs::derive`). It is the only way the mdoc roles build one, so
/// neither role opens a transcript on unchecked values (mdoc I2).
pub(super) fn statement<'s, DH, DS>(
    composition: &'s Composition<'_, DH, DS>,
    request: &'s Request<'_>,
    public: &'s PublicInputs,
) -> Result<MdocStatement<'s, DH, DS>, String>
where
    DH: EvaluationDomain<2, Gf2_128Field>,
    DS: EvaluationDomain<4, P256Field>,
{
    composition.statement(Identity::of(request), public.hash(), public.signature())
}

#[cfg(test)]
mod tests;
