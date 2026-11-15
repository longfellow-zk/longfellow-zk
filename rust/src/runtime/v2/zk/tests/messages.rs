// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Every prover message of a standalone proof is absorbed where it is sent,
//! before the next draw (transcript I4, I7); see `proto::tests::messages`.
use std::collections::BTreeSet;

use super::{circuit, prove_standalone};
use crate::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{
            packing::{PackingExtension, PackingField},
            range_interpolation::EvaluationDomain,
            ZkField,
        },
        random::DeterministicRng,
        v2::{
            proto::{
                polygero::PolygeroConfig,
                tags::Tag,
                tests::messages::{check_absorbed, sent},
                zk::ZkProof,
            },
            transcript::{Opened, Trace, VerifiedProof},
            zk::{CircuitInput, ZkContext, ZkProver, ZkVerifier},
        },
    },
};

const CONTEXT: &[u8] = b"longfellow/v2/test/messages";
const CONFIG: PolygeroConfig = PolygeroConfig {
    k: 8,
    s: 2,
    n: 64,
    t: 2,
};

/// A complete standalone proof of the test circuit, its public inputs and
/// a verifier of it.
pub(super) struct Standalone<const W: usize, F: ZkField<W> + PackingField> {
    pub(super) bytes: Vec<u8>,
    pub(super) public: Vec<CircuitInput<F>>,
    pub(super) verifier: ZkVerifier<W, F>,
}
impl<const W: usize, F: ZkField<W> + PackingField> Standalone<W, F> {
    pub(super) fn new<D: EvaluationDomain<W, F>>(f: &F, ctx: &ZkContext<'_, W, F, D>) -> Self {
        let extension = f.packing_extension();
        let base = extension.base();
        let public = vec![base.one()];
        let prover = ZkProver::new(circuit(f), CONFIG, ctx).unwrap();
        let (proof, geometry, t) = prove_standalone(
            &prover,
            CONTEXT,
            &public,
            vec![base.one(), base.one()],
            ctx,
            &mut DeterministicRng::new(42),
        )
        .unwrap();
        Self {
            bytes: proof.write(&geometry, f, t).unwrap().into_bytes(),
            public,
            verifier: ZkVerifier::new(circuit(f), CONFIG, ctx).unwrap(),
        }
    }
    /// The complete verification of `bytes`: open the session, parse
    /// against its geometry, verify and check the seal.
    pub(super) fn verify<D: EvaluationDomain<W, F>>(
        &self,
        bytes: &[u8],
        f: &F,
        ctx: &ZkContext<'_, W, F, D>,
    ) -> Result<VerifiedProof, String> {
        let statement = self
            .verifier
            .statement(CONTEXT, &self.public)
            .map_err(|e| e.to_string())?;
        let mut session = Opened::new(&statement);
        let parsed = ZkProof::read(bytes, &session.geometry(), f).map_err(|e| e.to_string())?;
        self.verifier
            .verify(session, parsed, ctx)
            .map_err(|e| e.to_string())
    }
}

/// Alter every prover message of the standalone proof in turn, one byte
/// where the proof carries it: each is absorbed as altered before the next
/// draw, which changes, and the proof is rejected.
fn every_message<const W: usize, F: ZkField<W> + PackingField, D: EvaluationDomain<W, F>>(
    f: &F,
    domain: &D,
    tags: &[Tag],
) {
    let ctx = ZkContext::new(domain);
    let proof = Standalone::new(f, &ctx);
    let verified = proof.verify(&proof.bytes, f, &ctx).unwrap();
    let honest = &verified.trace;
    let messages = sent(honest, 4);
    let seen: BTreeSet<u64> = messages.iter().map(|m| m.tag).collect();
    assert_eq!(seen, tags.iter().map(|t| t.value()).collect());
    let verify = |altered: &[u8]| {
        let (result, traces) = Trace::dropped(|| proof.verify(altered, f, &ctx));
        (result.is_ok(), traces)
    };
    for m in &messages {
        check_absorbed(honest, &proof.bytes, m, &verify);
    }
}

#[test]
fn binary_prover_messages_are_absorbed() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    every_message(
        &f,
        &BinaryInterpolatorFactory::full_field(&f),
        &[
            Tag::Commitment,
            Tag::FingerprintResponse,
            Tag::SumcheckRound,
            Tag::SumcheckCross,
            Tag::SumcheckClaims,
            Tag::PackingU,
            Tag::PackingA,
            Tag::PolygeroResponse,
        ],
    );
}

#[test]
fn prime_prover_messages_are_absorbed() {
    use crate::runtime::algebra::{
        fp2::Fp2Field, p256::P256Field,
        range_interpolation::QuadraticExtensionFftInterpolatorFactory, SupportsFFT,
    };
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    // Degree one: no packing messages.
    every_message(
        &f,
        &QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order()),
        &[
            Tag::Commitment,
            Tag::FingerprintResponse,
            Tag::SumcheckRound,
            Tag::SumcheckCross,
            Tag::SumcheckClaims,
            Tag::PolygeroResponse,
        ],
    );
}

/// The PRF block `Trace::first_block` computes is the strand's: for the
/// first node of a trace, the first block of the strand that hashed it.
#[test]
fn first_block_is_the_strands_first_prf_block() {
    use crate::runtime::{
        algebra::{gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory},
        v2::transcript::Strand,
    };
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let ctx = ZkContext::new(&d);
    let proof = Standalone::new(&f, &ctx);
    let verified = proof.verify(&proof.bytes, &f, &ctx).unwrap();
    let trace = &verified.trace;
    // The root's header is 16 bytes (u32 STRAND, u64 id 0, u32 no parent);
    // a continuation's adds its parent's digest.
    let mut root = Strand::new();
    root.write(&trace.nodes[0][16..]);
    let (mut prf, mut next) = root.continue_strand();
    assert_eq!(prf.next_block(), trace.first_block(0));
    next.write(&trace.nodes[1][16 + 32..]);
    assert_eq!(next.end_strand().next_block(), trace.first_block(1));
}
