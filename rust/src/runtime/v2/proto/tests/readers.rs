// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::super::{
    sumcheck::{SumcheckProof, SumcheckProofGeometry},
    MerkleProof,
};
use crate::core::algebra::{BareField, FieldID, SerializableField};

#[test]
fn merkle_frontier_is_its_count_of_digests_within_the_checked_path_bound() {
    let mut frontier = 3u64.to_le_bytes().to_vec();
    frontier.extend([7u8; 96]);
    frontier.push(9);
    let mut rest = &frontier[..];
    assert_eq!(MerkleProof::read_path(&mut rest, 3, 1).unwrap().len(), 3);
    // The count says where the frontier ends; the caller checks what follows.
    assert_eq!(rest, [9]);
    assert!(MerkleProof::read_path(&mut &frontier[..], 2, 1).is_err());
    assert!(MerkleProof::read_path(&mut &frontier[..103], 3, 1).is_err());
    assert!(MerkleProof::read_path(&mut &frontier[..7], 3, 1).is_err());
    assert!(MerkleProof::read_path(&mut &frontier[..], usize::MAX, 2).is_err());
}

struct ZeroWidth;
impl BareField for ZeroWidth {
    type E = u64;
}
impl SerializableField for ZeroWidth {
    fn field_id(&self) -> FieldID {
        FieldID::None
    }
    fn is_binary(&self) -> bool {
        false
    }
    fn serialized_size_bytes(&self) -> usize {
        0
    }
    fn to_bytes_into(&self, _: &u64, _: &mut [u8]) {}
    fn bytes_to_element(&self, _: &[u8]) -> Result<u64, String> {
        Ok(0)
    }
    fn serialized_mone(&self) -> Vec<u8> {
        Vec::new()
    }
}
#[test]
fn sumcheck_rejects_a_zero_width_codec_before_decoding() {
    let geometry = SumcheckProofGeometry::new(vec![]).unwrap();
    assert!(SumcheckProof::<2, ZeroWidth>::read(&mut &[][..], &geometry, &ZeroWidth).is_err());
}

/// Proof geometry is valid by construction and holds one Polygero profile
/// (proto I8): every field's Polygero geometry is derived from it.
#[test]
fn proof_geometries_are_checked_and_derive_their_polygero_geometry() {
    use super::super::{
        composed::ComposedGeometry,
        polygero::{PolygeroConfig, PolygeroGeometry},
        zk::{CircuitGeometry, ZkProofGeometry},
    };
    let config = PolygeroConfig {
        k: 2,
        s: 0,
        n: 4,
        t: 1,
    };
    let sumcheck = || SumcheckProofGeometry::new(vec![1, 0]).unwrap();
    assert!(CircuitGeometry::new(sumcheck(), 0, 3).is_err());
    let host = CircuitGeometry::new(sumcheck(), 2, 3).unwrap();
    let split = CircuitGeometry::new(sumcheck(), 1, 5).unwrap();
    assert_eq!(
        (host.sumcheck(), host.packing_degree(), host.nw()),
        (&sumcheck(), 2, 3)
    );

    let standalone = ZkProofGeometry::new(host.clone(), config).unwrap();
    assert_eq!(standalone.config(), config);
    assert_eq!(
        standalone.polygero(),
        PolygeroGeometry::new(3, config).unwrap()
    );
    let composed = ComposedGeometry::new(host.clone(), split.clone(), config).unwrap();
    assert_eq!(composed.config(), config);
    assert_eq!(
        composed.polygero(),
        [3, 5].map(|nw| PolygeroGeometry::new(nw, config).unwrap())
    );

    // A profile invalid for the cells is rejected, not stored.
    let invalid = PolygeroConfig { t: 2, ..config };
    assert!(ZkProofGeometry::new(host.clone(), invalid).is_err());
    assert!(ComposedGeometry::new(host.clone(), split.clone(), invalid).is_err());
    let too_large = CircuitGeometry::new(sumcheck(), 1, usize::MAX).unwrap();
    assert!(ZkProofGeometry::new(too_large.clone(), config).is_err());
    assert!(ComposedGeometry::new(host.clone(), too_large, config).is_err());
    // A split frontend has no packing response (audit P3).
    assert!(ComposedGeometry::new(split, host, config).is_err());
}

/// The composed writer emits exactly the bodies its length calculator and
/// reader accept (audit P3): a split packing degree other than one is not a
/// geometry, so it cannot reach the writer.
#[test]
fn composed_writer_and_reader_agree_on_every_constructible_geometry() {
    use super::super::{
        composed::{AdapterMessage, ComposedGeometry, ComposedProof},
        dual_packing::PackingProof,
        polygero::{FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig},
        witness_selection::FingerprintResponse,
        zk::{CircuitGeometry, CircuitProof},
        Digest, MerkleNonce,
    };
    use crate::{core::algebra::AlgebraicField, runtime::algebra::gf2_128::Gf2_128Field};
    #[derive(Debug, PartialEq)]
    struct Empty;
    impl AdapterMessage for Empty {
        const BYTES: usize = 0;
        fn write(&self, _: &mut Vec<u8>) {}
    }
    impl super::super::composed::sealed::Read for Empty {
        fn read(_: &mut &[u8]) -> Result<Self, String> {
            Ok(Self)
        }
    }
    type Body = ComposedProof<2, Gf2_128Field, 2, Gf2_128Field, Empty>;
    let f = Gf2_128Field::new();
    let config = PolygeroConfig {
        k: 2,
        s: 0,
        n: 4,
        t: 1,
    };
    let sumcheck = || SumcheckProofGeometry::new(vec![]).unwrap();
    let circuit = |degree| CircuitGeometry::new(sumcheck(), degree, 0).unwrap();
    assert!(ComposedGeometry::new(circuit(1), circuit(2), config).is_err());
    let g = ComposedGeometry::new(circuit(1), circuit(1), config).unwrap();
    let body = || FieldProof {
        h: vec![f.zero(); 2],
        z: vec![f.zero(); 4],
        rows: vec![f.zero(); 3],
    };
    let fingerprint = || FingerprintResponse {
        values: [f.zero(); 2],
    };
    let proof: Body = ComposedProof {
        commitment: PolygeroCommitment {
            root: Digest::default(),
        },
        fingerprints: (fingerprint(), (fingerprint(), ())),
        split: SumcheckProof { layers: vec![] },
        mu: f.zero(),
        message: Empty,
        host: CircuitProof {
            sumcheck_proof: SumcheckProof { layers: vec![] },
            packing: PackingProof::Direct,
        },
        polygero: JointPolygeroProof {
            bodies: (body(), (body(), ())),
            opening: MerkleProof {
                nonce: vec![MerkleNonce { bytes: [0; 32] }],
                path: vec![],
            },
        },
    };
    let mut out = Vec::new();
    proof.write_to_buf(&mut out, &g, &f, &f).unwrap();
    assert_eq!(Some(out.len() - 8), Body::fixed_len(&g, &f, &f));
    assert_eq!(Body::read(&out, &g, &f, &f).unwrap(), proof);
}
