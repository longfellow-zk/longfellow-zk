// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The composition driver on tiny circuits, independent of any application.
//!
//! The P-256 split circuit asserts `x0 = x1` over private inputs `[x0, x1]`;
//! `x0` is stored as 8 bits of the binary host's private input and `x1` is
//! native. The host circuit asserts that bit 0 equals its public input.
use super::Composition;
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField, SupportsU64Conversions},
        proto::v2::{Circuit, Layer, Linear, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::{
            fp2::Fp2Field,
            gf2_128::Gf2_128Field,
            p256::P256Field,
            range_interpolation::{
                BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            },
            SupportsFFT,
        },
        random::DeterministicRng,
        v2::{
            foreign::{adapter::p256::P256Mode, word::MaskedWord},
            polygero::PolygeroConfig,
            transcript::Transcript,
            zk::{
                split::value_count,
                storage::{Group, StorageMap},
            },
        },
    },
};

/// Bits of the shared value `x0`.
const WIDTH: usize = 8;
/// The claim reads `x0` and the 256 bits of R: 264 <= 2^9.
type Mode = P256Mode<9>;
const CONFIG: PolygeroConfig = PolygeroConfig {
    k: 64,
    s: 2,
    n: 256,
    t: 8,
};
const LABEL: &[u8] = b"foreign/compose-test";

/// One layer whose single output, asserted zero, is the sum of
/// `k[c] * input[l]` over `terms` `(l, c)`. Input 0 is public.
fn circuit<F: SerializableField>(
    f: &F,
    ninput: usize,
    k: Vec<F::E>,
    terms: &[(u32, u32)],
) -> Circuit<F> {
    let raw = RawCircuitBuilder {
        ninput,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: k,
        layers: vec![Layer::with_assertions(
            ninput,
            Stream::default(),
            Stream::<Linear>::from_terms(terms.iter().map(|&(l, k)| Linear { g: 0, l, k })),
            Stream::default(),
            |_| false,
        )],
    }
    .build();
    Circuit::from_raw(f, raw)
}

#[test]
fn composition_round_trip_rejects_tampering() {
    let gf2 = Gf2_128Field::new();
    let p = P256Field::new();
    let p2 = Fp2Field::new(&p);
    let host_domain = BinaryInterpolatorFactory::full_field(&gf2);
    let split_domain =
        QuadraticExtensionFftInterpolatorFactory::new(&p, &p2, p2.omega(), p2.omega_order());
    // Host: input[0] + input[1] = 0, so bit 0 of x0 is one.
    let host = circuit(&gf2, 1 + WIDTH, vec![gf2.one()], &[(0, 0), (1, 0)]);
    // Split: input[1] - input[2] = 0, so x0 = x1.
    let split = circuit(&p, 3, vec![p.one(), p.mone()], &[(1, 0), (2, 1)]);
    let shared = Group {
        start: 1,
        width: WIDTH,
    };
    let storage = StorageMap::new(value_count(&split).unwrap(), &[(0, shared)]).unwrap();
    let c = Composition::<4, P256Field, _, _, Mode>::new(
        &host,
        &split,
        storage,
        (CONFIG, CONFIG),
        (&host_domain, &split_domain),
    )
    .unwrap();

    let x = 0xa5u64;
    let bits: Vec<bool> = (0..WIDTH).map(|j| (x >> j) & 1 != 0).collect();
    let prove = |host_private: Vec<bool>| {
        let value = p.u64_to_element(x);
        c.prove(
            &[true],
            host_private,
            &[p.one()],
            vec![value, value],
            Transcript::new(LABEL),
            &mut DeterministicRng::new(5),
        )
    };
    let verify = |proof: &_| c.verify(&[true], &[p.one()], proof, Transcript::new(LABEL));

    let (proof, mut tp) = prove(bits.clone()).unwrap();
    let mut tv = verify(&proof).unwrap();
    assert_eq!(tp.bytes(32), tv.bytes(32));

    // A changed split message mu.
    let mut bad = proof.clone();
    p.add(&mut bad.mu, &p.one());
    assert!(verify(&bad).is_err());

    // A changed masked quotient in the adapter's message.
    let mut bad = proof.clone();
    let mut bytes = bad.message[0].encoded();
    bytes[0] ^= 1;
    bad.message[0] = MaskedWord::read(&mut bytes.as_slice()).unwrap();
    assert!(verify(&bad).is_err());

    // A host bit inconsistent with x0, which the host circuit itself does not
    // read: the adapter's trees fail, so the honest prover cannot proceed.
    let mut inconsistent = bits;
    inconsistent[3] ^= true;
    assert!(prove(inconsistent).is_err());
}
