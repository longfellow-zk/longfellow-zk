// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Immutable ML-DSA setup and independent uniform public-key projections.
use super::*;
use crate::{
    mldsa::{proto::CLAIMS, runtime::projection},
    runtime::v2::{
        proto::tags::Tag,
        transcript::{
            Encoder, Header, Message, SetupMessage, Statement, Transcript, TranscriptRef,
        },
    },
};
pub(super) struct WithSetup<I, W> {
    pub identity: I,
    pub setup: W,
}
impl<I: SetupMessage, W: Fn(&mut Header<'_>)> Statement for WithSetup<I, W> {
    type Identity = I;
    fn identity(&self) -> &I {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        (self.setup)(h);
    }
}
struct PublicIdentity<'a> {
    c: &'a Circuits,
    context: &'a [u8],
    encoded: Vec<u8>,
    k: usize,
    l: usize,
}
impl Message for PublicIdentity<'_> {
    const TAG: Tag = Tag::MldsaPublicStatement;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.bytes(b"longfellow/mldsa/public-linear/foreign/v2");
        e.bytes(self.context);
        e.nats(&[self.k as u64, self.l as u64]);
        e.bytes(&self.c.binary.id);
        e.bytes(self.c.keccak.label().as_bytes());
        e.bytes(&self.encoded);
    }
}
impl SetupMessage for PublicIdentity<'_> {}
pub(super) fn start<P: MlDsaParams>(
    c: &Circuits,
    key: &PublicKey,
    context: &[u8],
    setup: impl Fn(&mut Header<'_>),
) -> Transcript {
    let mut encoded = Vec::new();
    for x in key
        .a_hat
        .iter()
        .flatten()
        .flatten()
        .chain(key.ntt_t1().iter().flatten())
    {
        encoded.extend_from_slice(&x.to_le_bytes());
    }
    Transcript::new(&WithSetup {
        identity: PublicIdentity {
            c,
            context,
            encoded,
            k: P::K,
            l: P::L,
        },
        setup,
    })
}
#[allow(clippy::needless_range_loop)]
pub(super) fn projections<P: MlDsaParams>(
    key: &PublicKey,
    t: &mut TranscriptRef<'_>,
) -> ExactClaims {
    let af = RuntimeFp24Ext6::new();
    let lambda = t.draw(|r| {
        let mut rows: [Vec<[u32; N]>; CLAIMS] = std::array::from_fn(|_| vec![[0; N]; P::K]);
        for row in 0..P::K {
            for col in 0..N {
                let x = r.elt_field(&af);
                for coordinate in 0..CLAIMS {
                    rows[coordinate][row][col] = x.coefficients()[coordinate];
                }
            }
        }
        rows
    });
    projection::project::<P>(&key.a_hat, &key.ntt_t1(), &lambda)
}
