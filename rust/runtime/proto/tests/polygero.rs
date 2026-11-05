// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        proto::{
            polygero::{self, PolygeroGeometry, PolygeroProof},
            MerkleNonce, MerkleProof,
        },
    },
};
fn geometry() -> PolygeroGeometry {
    PolygeroGeometry {
        nw: 6,
        nq: 0,
        k: 4,
        s: 1,
        n: 16,
        t: 1,
    }
}
fn proof(g: &PolygeroGeometry, field: &Gf2_128Field) -> PolygeroProof<Gf2_128> {
    PolygeroProof {
        h: vec![field.zero(); g.k + g.s],
        z: vec![field.one(); 2 * g.k],
        rows: (0..g.t * g.transmitted_rows())
            .map(|i| Gf2_128::from((i as u128) << 100))
            .collect(),
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
            nq: 3,
            k: 8,
            t: 2,
            ..geometry()
        },
    ] {
        let p = proof(&g, &f);
        let bytes = p.write(&g, &f).unwrap();
        assert_eq!(&bytes[..4], b"PLG8");
        let offset = 28 + (p.h.len() + p.z.len()) * 16;
        let expected = p
            .rows
            .iter()
            .flat_map(|x| f.to_bytes(x))
            .collect::<Vec<_>>();
        assert_eq!(&bytes[offset..bytes.len() - 32 * g.t - 4], expected);
        assert_eq!(
            bytes.len(),
            28 + (p.h.len() + p.z.len() + p.rows.len()) * 16 + 32 * g.t + 4
        );
        let mut concat = bytes.clone();
        concat.extend_from_slice(&bytes);
        let mut input = concat.as_slice();
        assert_eq!(polygero::read(&mut input, &g, &f).unwrap(), p);
        assert_eq!(input, bytes);
        assert_eq!(polygero::read(&mut input, &g, &f).unwrap(), p);
        assert!(input.is_empty());
        let mut bad = p.clone();
        bad.rows.push(f.zero());
        assert!(bad.write(&g, &f).is_err());
    }
}
#[test]
fn malformed_geometry_frontier_versions_and_every_truncation_are_rejected() {
    let f = Gf2_128Field::new();
    let g = geometry();
    let p = proof(&g, &f);
    let bytes = p.write(&g, &f).unwrap();
    for n in 0..bytes.len() {
        assert!(
            polygero::read(&mut &bytes[..n], &g, &f).is_err(),
            "length {n}"
        );
    }
    for marker in [b"PLG7", b"PLG6", b"PYG2"] {
        let mut bad = bytes.clone();
        bad[..4].copy_from_slice(marker);
        assert!(polygero::read(&mut bad.as_slice(), &g, &f).is_err());
    }
    let mut bad = bytes.clone();
    bad[4..8].copy_from_slice(&7u32.to_le_bytes());
    assert!(polygero::read(&mut bad.as_slice(), &g, &f).is_err());
    let mut invalid_frontier = bytes.clone();
    let n = invalid_frontier.len();
    invalid_frontier[n - 4..].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(polygero::read(&mut invalid_frontier.as_slice(), &g, &f).is_err());
}
// An ambient codec accepting aliases must still be checked canonically.
struct Aliased(Gf2_128Field);
impl crate::core::algebra::BareField for Aliased {
    type E = Gf2_128;
}
impl SerializableField for Aliased {
    fn is_binary(&self) -> bool {
        true
    }
    fn serialized_size_bytes(&self) -> usize {
        16
    }
    fn to_bytes_into(&self, x: &Gf2_128, dst: &mut [u8]) {
        self.0.to_bytes_into(x, dst)
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<Gf2_128, String> {
        if b == [0xff; 16] {
            Ok(self.0.zero())
        } else {
            self.0.bytes_to_element(b)
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        self.0.serialized_mone()
    }
}
#[test]
fn noncanonical_ambient_elements_are_rejected() {
    let f = Gf2_128Field::new();
    let mut b = proof(&geometry(), &f).write(&geometry(), &f).unwrap();
    b[28..44].fill(0xff);
    assert!(polygero::read(&mut b.as_slice(), &geometry(), &Aliased(f)).is_err());
}
