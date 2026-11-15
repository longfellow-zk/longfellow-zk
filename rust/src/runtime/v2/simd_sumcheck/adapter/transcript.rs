// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::{
    proto::tags::Tag,
    transcript::{Encoder, Message, ProverMessage},
};
struct TraceU<'a>(&'a [E; 128], &'a F);
impl Message for TraceU<'_> {
    const TAG: Tag = Tag::SimdTraceU;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.1, self.0);
    }
}
impl ProverMessage for TraceU<'_> {}
struct TraceA<'a>(&'a E, &'a F);
impl Message for TraceA<'_> {
    const TAG: Tag = Tag::SimdTraceA;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.elements(self.1, std::slice::from_ref(self.0));
    }
}
impl ProverMessage for TraceA<'_> {}
pub(super) fn challenges(
    _claim: &Claim,
    proof: &Proof,
    _id: &[u8; 32],
    t: &mut TranscriptRef<'_>,
    f: &F,
) -> [E; 128] {
    t.send(&TraceU(&proof.u, f));
    t.draw(|r| std::array::from_fn(|_| r.elt_field(f)))
}
pub(super) fn finish(a: E, t: &mut TranscriptRef<'_>, f: &F) {
    t.send(&TraceA(&a, f));
}
