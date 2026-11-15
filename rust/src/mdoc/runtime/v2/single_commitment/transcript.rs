// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The parser-free single-commitment identity, fixed before proof decoding.
use crate::{
    mdoc::v2::{request::Request, ZkSpecStruct},
    runtime::v2::{
        proto::tags::Tag,
        transcript::{Encoder, Message, SetupMessage},
    },
};

pub(super) struct Identity<'a> {
    session: &'a [u8],
    spec: &'a ZkSpecStruct,
}
impl<'a> Identity<'a> {
    pub(super) fn of(request: &Request<'a>) -> Self {
        Self {
            session: request.transcript(),
            spec: request.spec(),
        }
    }
}
impl Message for Identity<'_> {
    const TAG: Tag = Tag::SingleCommitmentStatement;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(b"longfellow/v2/mdoc/single-commitment/no-parser/transcript/v2");
        e.bytes(self.session);
        e.bytes(&self.spec.combined_hash);
        e.nats(&[self.spec.version as u64, self.spec.num_attributes as u64]);
    }
}
impl SetupMessage for Identity<'_> {}
