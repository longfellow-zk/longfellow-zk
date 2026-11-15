// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::fixtures::Aliased;
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        v2::proto::{
            polygero::{FieldProof, JointPolygeroProof, PolygeroGeometry},
            Digest, MerkleNonce, MerkleProof, NONCE_LEN,
        },
    },
};
fn geometry() -> PolygeroGeometry {
    PolygeroGeometry {
        nw: 6,
        k: 4,
        s: 1,
        n: 16,
        t: 1,
    }
}
fn proof(
    g: &PolygeroGeometry,
    field: &Gf2_128Field,
) -> JointPolygeroProof<(FieldProof<Gf2_128>, ())> {
    JointPolygeroProof {
        bodies: (
            FieldProof {
                h: vec![field.zero(); g.k + g.s],
                z: vec![field.one(); 2 * g.k],
                rows: (0..g.t * g.nrow())
                    .map(|i| Gf2_128::from((i as u128) << 100))
                    .collect(),
            },
            (),
        ),
        opening: MerkleProof {
            nonce: vec![
                MerkleNonce {
                    bytes: [0x57; NONCE_LEN]
                };
                g.t
            ],
            path: vec![],
        },
    }
}
#[test]
fn ambient_rows_have_fixed_width_and_preserve_order() {
    let f = Gf2_128Field::new();
    for g in [
        geometry(),
        PolygeroGeometry {
            nw: 3,
            k: 8,
            t: 2,
            ..geometry()
        },
    ] {
        let p = proof(&g, &f);
        let bytes = write(&p, &g, &f).unwrap();
        // The response, then the rows, then the nonces, then the frontier's
        // count (here zero); no magic.
        let offset = (p.bodies.0.h.len() + p.bodies.0.z.len()) * 16;
        let expected = p
            .bodies
            .0
            .rows
            .iter()
            .flat_map(|x| f.to_bytes(x))
            .collect::<Vec<_>>();
        assert_eq!(&bytes[offset..bytes.len() - NONCE_LEN * g.t - 8], expected);
        assert_eq!(bytes[bytes.len() - 8..], [0; 8]);
        assert_eq!(
            bytes.len(),
            (p.bodies.0.h.len() + p.bodies.0.z.len() + p.bodies.0.rows.len()) * 16
                + NONCE_LEN * g.t
                + 8
        );
        assert_eq!(read(&mut bytes.as_slice(), &g, &f).unwrap(), p);
        let mut bad = p.clone();
        bad.bodies.0.rows.push(f.zero());
        assert!(write(&bad, &g, &f).is_err());
    }
}
#[test]
fn malformed_frontiers_and_every_truncation_are_rejected() {
    let f = Gf2_128Field::new();
    let g = geometry();
    let p = proof(&g, &f);
    let bytes = write(&p, &g, &f).unwrap();
    for n in 0..bytes.len() {
        assert!(read(&mut &bytes[..n], &g, &f).is_err(), "length {n}");
    }
    // The frontier carries its count, so no extension parses either: not a
    // partial digest, not a whole one, and not a count above the cap.
    for extra in [1, 31, 32, 33, 64] {
        let mut longer = bytes.clone();
        longer.extend(std::iter::repeat_n(0, extra));
        assert!(
            read(&mut longer.as_slice(), &g, &f).is_err(),
            "{extra} extra bytes"
        );
    }
    let mut counted = bytes.clone();
    let n = counted.len();
    counted[n - 8] = 1;
    counted.extend_from_slice(&[0; 32]);
    assert!(read(&mut counted.as_slice(), &g, &f).is_ok());
    let cap = g.t * (g.n.next_power_of_two().trailing_zeros() as usize + 1);
    let mut over = bytes.clone();
    over[n - 8..].copy_from_slice(&(cap as u64 + 1).to_le_bytes());
    over.extend(std::iter::repeat_n(0, 32 * (cap + 1)));
    assert!(read(&mut over.as_slice(), &g, &f).is_err());
}
#[test]
fn noncanonical_ambient_elements_are_rejected() {
    let f = Gf2_128Field::new();
    let mut b = write(&proof(&geometry(), &f), &geometry(), &f).unwrap();
    b[0..16].fill(0xff);
    assert!(read(&mut b.as_slice(), &geometry(), &Aliased(f)).is_err());
}

fn write<F: SerializableField>(
    p: &JointPolygeroProof<(FieldProof<F::E>, ())>,
    g: &PolygeroGeometry,
    f: &F,
) -> std::io::Result<Vec<u8>> {
    let mut out = Vec::new();
    p.write_to_buf(
        &mut out,
        g.t,
        g.n,
        |b, out| b.0.write_response(out, g, f),
        |b, out| b.0.write_rows(out, g, f),
    )?;
    Ok(out)
}
/// Read a whole body, as a complete reader does after its length check.
fn read<F: SerializableField>(
    bytes: &mut &[u8],
    g: &PolygeroGeometry,
    f: &F,
) -> std::io::Result<JointPolygeroProof<(FieldProof<F::E>, ())>> {
    JointPolygeroProof::read(
        bytes,
        g.t,
        g.n,
        |bytes| Ok((FieldProof::read_response(bytes, g, f)?, ())),
        |b, bytes| b.0.read_rows(bytes, g, f),
    )
}

#[test]
fn oversized_opening_counts_reject_without_allocation() {
    let bytes = [0u8; 64];
    for (t, n) in [(1 << 28, 1 << 28), (usize::MAX, usize::MAX), (0, 0)] {
        let result = JointPolygeroProof::<()>::read::<std::io::Error>(
            &mut bytes.as_slice(),
            t,
            n,
            |_| Ok(()),
            |_, _| Ok(()),
        );
        assert!(result.is_err());
    }
}

#[test]
fn the_length_check_bounds_the_frontier_before_decoding() {
    use super::super::polygero::checked_body;
    // t = 2 columns of n = 16 leaves: at most 2 * 5 frontier digests. The
    // count follows the 4 + 10 bytes before the frontier.
    let frame = 4 + 10 + 8 + 32;
    let proof = |count: u64, digests: usize| {
        let mut bytes = vec![0u8; 14];
        bytes.extend(count.to_le_bytes());
        bytes.resize(frame + 32 * digests, 0);
        bytes
    };
    for digests in 0..=10 {
        let bytes = proof(digests as u64, digests);
        let body = checked_body(&bytes, 4, 10, 2, 16).unwrap();
        assert_eq!(body.len(), 10 + 8 + 32 * digests);
        // Every other length fails, whole digests included.
        for len in 0..bytes.len() + 64 {
            if len != bytes.len() {
                let mut other = bytes.clone();
                other.resize(len, 0);
                assert!(checked_body(&other, 4, 10, 2, 16).is_err(), "length {len}");
            }
        }
    }
    // A count above the cap, or one too large for usize, fails.
    assert!(checked_body(&proof(11, 11), 4, 10, 2, 16).is_err());
    assert!(checked_body(&proof(u64::MAX, 0), 4, 10, 2, 16).is_err());
    assert!(checked_body(&[0; 64], usize::MAX, 1, 2, 16).is_err());
}

#[test]
fn nonce_codec_uses_the_full_salt_width_and_preserves_the_following_message() {
    assert_eq!(NONCE_LEN, 32);
    let nonces = vec![
        MerkleNonce {
            bytes: std::array::from_fn(|i| i as u8),
        },
        MerkleNonce {
            bytes: [0xa7; NONCE_LEN],
        },
    ];
    let p = MerkleProof {
        nonce: nonces.clone(),
        path: vec![Digest::default()],
    };
    let mut bytes = Vec::new();
    p.write_nonces(&mut bytes);
    assert_eq!(bytes.len(), NONCE_LEN * nonces.len());
    p.write_path(&mut bytes);
    assert_eq!(bytes.len(), NONCE_LEN * nonces.len() + 8 + 32);
    let mut input = bytes.as_slice();
    assert_eq!(
        MerkleProof::read_nonces(&mut input, nonces.len()).unwrap(),
        nonces
    );
    assert_eq!(MerkleProof::read_path(&mut input, 2, 4).unwrap(), p.path);
    assert!(input.is_empty());
    for count in [nonces.len(), usize::MAX] {
        assert!(MerkleProof::read_nonces(&mut &bytes[..NONCE_LEN * 2 - 1], count).is_err());
    }
    let proof = JointPolygeroProof {
        bodies: (),
        opening: p,
    };
    assert_eq!(proof.authentication_bytes(), (2 * NONCE_LEN, 8 + 32));
    // The mdoc profile opens 84 shared columns with one 32-byte salt each.
    assert_eq!(84 * NONCE_LEN, 2688);
}
