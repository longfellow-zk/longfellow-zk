// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    mldsa::{proto::MlDsaParams, runtime::transcript::WithSetup},
    runtime::{
        algebra::gf2_128::Gf2_128 as B,
        v2::{
            proto::tags::Tag,
            transcript::{Encoder, Header, Message, SetupMessage, Transcript, TranscriptRef},
        },
    },
};
struct Identity<'a> {
    c: &'a Circuits,
    context: &'a [u8],
    k: usize,
    l: usize,
}
impl Message for Identity<'_> {
    const TAG: Tag = Tag::MldsaHiddenStatement;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(b"mldsa/hidden-key/foreign/v2");
        e.bytes(self.context);
        e.nats(&[self.k as u64, self.l as u64]);
        e.bytes(&self.c.binary.id);
        e.bytes(&self.c.arithmetic.id);
        e.bytes(self.c.keccak.label().as_bytes());
    }
}
impl SetupMessage for Identity<'_> {}
pub(super) fn start<P: MlDsaParams>(
    c: &Circuits,
    context: &[u8],
    setup: impl Fn(&mut Header<'_>),
) -> Transcript {
    Transcript::new(&WithSetup {
        identity: Identity {
            c,
            context,
            k: P::K,
            l: P::L,
        },
        setup,
    })
}
pub(super) fn gamma(t: &mut TranscriptRef<'_>) -> Vec<B> {
    t.draw(|r| r.elements(&Gf2_128Field::new(), 2).collect())
}
