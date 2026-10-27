// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use crate::{
    core::{
        bits::PackedBits,
        proto::{
            circuit::{compute_id, RawCircuit},
            Layer, TermDelta,
        },
    },
    runtime::{
        algebra::{range_interpolation::BinaryInterpolatorFactory, subfield::BinarySubfield},
        random::DeterministicRng,
    },
};
fn circuit() -> Circuit<F> {
    let f = F::new();
    let raw = RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one()],
        layers: vec![Layer::new_compressed(
            3,
            2,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [0, 0],
                    k_index: 0,
                },
                TermDelta {
                    g: 0,
                    h: [1, 2],
                    k_index: 0,
                },
            ]],
            vec![0],
        )],
    };
    let id = compute_id(&f, &raw);
    Circuit { raw, id }
}
#[test]
fn end_to_end_packed_commitment_and_adversarial_changes() {
    let f = F::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let ctx = ZkContext {
        f: &f,
        domain: &domain,
    };
    let cfg = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let protocol = PackedCircuit::new(circuit(), cfg, 1, [42; 32]).unwrap();
    let public = vec![f.one()];
    let extra = vec![AuxiliaryBitClaim {
        weights: vec![f.one(), f.zero()],
        rhs: AffineClaim {
            constant: f.zero(),
            terms: vec![(0, f.one())],
        },
    }];
    let mut t = Transcript::new(b"packed-test");
    let (state, geom) = protocol
        .commit(
            [true, true].into_iter().collect::<PackedBits>(),
            vec![f.one()],
            &ctx,
            &mut t,
            &mut DeterministicRng::new(42),
            &sf,
        )
        .unwrap();
    assert_eq!(protocol.layout.packed_words, 1);
    assert_eq!(protocol.layout.gkr_start, 130);
    let proof = protocol
        .prove(&public, &extra, state, &mut t, &ctx)
        .unwrap();
    let bytes = proof.write(&geom, &f, &sf).unwrap();
    assert_eq!(&bytes[..4], b"LFB2");
    let mut obsolete = bytes.clone();
    obsolete[..4].copy_from_slice(b"LFB1");
    assert!(PackedZkProof::read(&mut obsolete.as_slice(), &geom, &f, &sf).is_err());
    let mut rest = bytes.as_slice();
    let decoded = PackedZkProof::read(&mut rest, &geom, &f, &sf).unwrap();
    assert!(rest.is_empty());
    for window in 1..=4 {
        let optimized = PackedCircuit::new(circuit(), cfg, 1, [42; 32])
            .unwrap()
            .with_boolean_window(window)
            .unwrap();
        let mut ts = Transcript::new(b"packed-test");
        let (committed, g) = optimized
            .commit(
                [true, true].into_iter().collect(),
                vec![f.one()],
                &ctx,
                &mut ts,
                &mut DeterministicRng::new(42),
                &sf,
            )
            .unwrap();
        let p = optimized
            .prove(&public, &extra, committed, &mut ts, &ctx)
            .unwrap();
        assert_eq!(p.write(&g, &f, &sf).unwrap(), bytes, "window={window}");
    }
    let mut verifier = PackedVerifier::new(
        PackedCircuit::new(circuit(), cfg, 1, [42; 32]).unwrap(),
        &ctx,
    )
    .unwrap();
    let mut verify = |p: &PackedZkProof, inputs: &[E], claims: &[AuxiliaryBitClaim]| {
        let mut v = Transcript::new(b"packed-test");
        verifier.receive_commitment(p, &mut v);
        verifier.verify(inputs, claims, p, &mut v, &ctx)
    };
    verify(&decoded, &public, &extra).unwrap();
    for level in 0..crate::runtime::dual_packing::DUAL_PACKING_MESSAGES {
        let mut bad = decoded.clone();
        bad.dual_packing_proof.messages[level].xor_in_place(&f.one());
        assert!(verify(&bad, &public, &extra).is_err());
    }
    let mut bad = decoded.clone();
    bad.com.root.data[0] ^= 1;
    assert!(verify(&bad, &public, &extra).is_err());
    assert!(verify(&decoded, &[f.zero()], &extra).is_err());
    assert!(verify(&decoded, &[E::from(2)], &extra).is_err());
    let changed = vec![AuxiliaryBitClaim {
        weights: extra[0].weights.clone(),
        rhs: AffineClaim {
            constant: f.one(),
            terms: vec![(0, f.one())],
        },
    }];
    assert!(verify(&decoded, &public, &changed).is_err());
    assert!(verify(&decoded, &public, &[]).is_err());
    for n in [0, 3, 4, 35, bytes.len() - 1] {
        assert!(PackedZkProof::read(&mut &bytes[..n], &geom, &f, &sf).is_err());
    }
}
