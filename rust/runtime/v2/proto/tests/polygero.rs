// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::fixtures::Aliased;
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        v2::proto::{
            polygero::{FieldProof, JointPolygeroProof, PolygeroGeometry},
            Digest, MerkleNonce, MerkleProof,
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
        context: Digest::default(),
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
            nonce: vec![MerkleNonce { bytes: [0x57; 32] }; g.t],
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
        assert_eq!(&bytes[..4], b"JPG2");
        let offset = 36 + (p.bodies.0.h.len() + p.bodies.0.z.len()) * 16;
        let expected = p
            .bodies
            .0
            .rows
            .iter()
            .flat_map(|x| f.to_bytes(x))
            .collect::<Vec<_>>();
        assert_eq!(&bytes[offset..bytes.len() - 32 * g.t - 4], expected);
        assert_eq!(
            bytes.len(),
            36 + (p.bodies.0.h.len() + p.bodies.0.z.len() + p.bodies.0.rows.len()) * 16
                + 32 * g.t
                + 4
        );
        let mut concat = bytes.clone();
        concat.extend_from_slice(&bytes);
        let mut input = concat.as_slice();
        assert_eq!(read(&mut input, &g, &f).unwrap(), p);
        assert_eq!(input, bytes);
        assert_eq!(read(&mut input, &g, &f).unwrap(), p);
        assert!(input.is_empty());
        let mut bad = p.clone();
        bad.bodies.0.rows.push(f.zero());
        assert!(write(&bad, &g, &f).is_err());
    }
}
#[test]
fn malformed_geometry_frontier_versions_and_every_truncation_are_rejected() {
    let f = Gf2_128Field::new();
    let g = geometry();
    let p = proof(&g, &f);
    let bytes = write(&p, &g, &f).unwrap();
    for n in 0..bytes.len() {
        assert!(read(&mut &bytes[..n], &g, &f).is_err(), "length {n}");
    }
    for marker in [b"PLG9", b"PLG8", b"PLG7", b"PLG6", b"PYG2"] {
        let mut bad = bytes.clone();
        bad[..4].copy_from_slice(marker);
        assert!(read(&mut bad.as_slice(), &g, &f).is_err());
    }
    let mut bad = bytes.clone();
    bad[4..8].copy_from_slice(&7u32.to_le_bytes());
    assert!(read(&mut bad.as_slice(), &g, &f).is_err());
    let mut invalid_frontier = bytes.clone();
    let n = invalid_frontier.len();
    invalid_frontier[n - 4..].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(read(&mut invalid_frontier.as_slice(), &g, &f).is_err());
}
#[test]
fn noncanonical_ambient_elements_are_rejected() {
    let f = Gf2_128Field::new();
    let mut b = write(&proof(&geometry(), &f), &geometry(), &f).unwrap();
    b[36..52].fill(0xff);
    assert!(read(&mut b.as_slice(), &geometry(), &Aliased(f)).is_err());
}

fn write<F: SerializableField>(
    p: &JointPolygeroProof<(FieldProof<F::E>, ())>,
    g: &PolygeroGeometry,
    f: &F,
) -> std::io::Result<Vec<u8>> {
    let mut out = Vec::new();
    p.write_to_buf(&mut out, &Digest::default(), g.t, g.n, |b, out| {
        b.0.write(out, g, f)
    })?;
    Ok(out)
}
fn read<F: SerializableField>(
    bytes: &mut &[u8],
    g: &PolygeroGeometry,
    f: &F,
) -> std::io::Result<JointPolygeroProof<(FieldProof<F::E>, ())>> {
    JointPolygeroProof::read(bytes, &Digest::default(), g.t, g.n, |bytes| {
        Ok((FieldProof::read(bytes, g, f)?, ()))
    })
}

#[test]
fn oversized_opening_counts_reject_without_allocation() {
    let mut bytes = b"JPG2".to_vec();
    bytes.extend_from_slice(&[0; 32]);
    for (t, n) in [(1 << 28, 1 << 28), (usize::MAX, usize::MAX), (0, 0)] {
        let result = JointPolygeroProof::<()>::read::<std::io::Error>(
            &mut bytes.as_slice(),
            &Digest::default(),
            t,
            n,
            |_| Ok(()),
        );
        assert!(result.is_err());
    }
}
