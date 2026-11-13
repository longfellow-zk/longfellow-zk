// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use sha2::Digest as _;

use super::*;
use crate::runtime::v2::proto::{MerkleNonce, NONCE_LEN};

#[test]
fn codecs_bind_role_index_context_and_salt() {
    let context = Digest::default();
    let other = Digest { data: [1; 32] };
    let salt = MerkleNonce {
        bytes: [7; NONCE_LEN],
    };
    let leaf = |context: &Digest, index, salt: &_| {
        let mut h = hash::leaf(context, index, salt);
        h.update(1u128.to_le_bytes());
        Digest {
            data: h.finalize().into(),
        }
    };
    let digest = leaf(&context, 0, &salt);
    assert_ne!(digest, leaf(&context, 1, &salt));
    assert_ne!(digest, leaf(&other, 0, &salt));
    let mut changed_salt = salt;
    changed_salt.bytes[0] ^= 1;
    assert_ne!(digest, leaf(&context, 0, &changed_salt));
    changed_salt = salt;
    changed_salt.bytes[NONCE_LEN - 1] ^= 1;
    assert_ne!(digest, leaf(&context, 0, &changed_salt));
    assert_ne!(digest, hash::node(&context, 1, &context, &other));
    let node = hash::node(&context, 1, &digest, &other);
    assert_ne!(node, hash::node(&context, 2, &digest, &other));
    assert_ne!(node, hash::node(&context, 1, &other, &digest));
    assert_ne!(node, hash::node(&other, 1, &digest, &other));
}

#[test]
fn independent_node_vector_binds_little_endian_u64_index() {
    // Generated independently with Python hashlib and struct '<Q'.
    let digest = hash::node(
        &Digest { data: [7; 32] },
        0x01020304,
        &Digest { data: [11; 32] },
        &Digest { data: [13; 32] },
    );
    assert_eq!(
        hex::encode(digest.data),
        "2877cd3899f0eb99df96aaf52f2c43da3275278b6b6ecd9b071e9834a8cbb03f"
    );
}

#[test]
fn independent_leaf_vector_pins_preimage_layout() {
    // Generated independently with printf and coreutils sha256sum over
    // "polygero/joint/leaf/v1" || [7; 32] || LE64(0x0102030405) || [9; 32]
    // followed by caller-appended column bytes [0xaa; 16] || [0xbb; 32].
    let mut h = hash::leaf(
        &Digest { data: [7; 32] },
        0x0102030405,
        &MerkleNonce {
            bytes: [9; NONCE_LEN],
        },
    );
    h.update([0xaa; 16]);
    h.update([0xbb; 32]);
    assert_eq!(
        hex::encode(h.finalize()),
        "748e94e279c0a2ff0c954e373bace13d5d1c54f7beaf7c182ed072fea45f4608"
    );
}

#[test]
fn indexed_heaps_support_unbalanced_trees_and_unsorted_openings() {
    let context = Digest { data: [3; 32] };
    // Identical digests deliberately exercise position binding without relying
    // on the leaf codec to distinguish the subtrees for us.
    for n in [1, 2, 3, 5, 8, 17] {
        let leaves = vec![Digest { data: [7; 32] }; n];
        let tree = MerkleHeap::new(&context, &leaves);
        for indices in [vec![0], vec![n - 1], (0..n).rev().collect()] {
            let path = tree.generate_proof(&indices);
            let opened: Vec<_> = indices.iter().map(|&i| (i, leaves[i])).collect();
            assert!(verify_proof(&context, n, &tree.root(), &path, &opened).is_ok());
        }
    }
}

#[test]
fn internal_nodes_cannot_be_moved_to_another_heap_position() {
    let context = Digest::default();
    let leaf = Digest { data: [7; 32] };
    let left = hash::node(&context, 2, &leaf, &leaf);
    let right = hash::node(&context, 3, &leaf, &leaf);
    assert_ne!(left, right);
    let tree = MerkleHeap::new(&context, &[leaf; 4]);
    assert_eq!(tree.root(), hash::node(&context, 1, &left, &right));
    let path = tree.generate_proof(&[0, 1]);
    assert_eq!(path, vec![right]);
    assert!(verify_proof(&context, 4, &tree.root(), &path, &[(0, leaf), (1, leaf)]).is_ok());
    assert!(verify_proof(&context, 4, &tree.root(), &[left], &[(0, leaf), (1, leaf)]).is_err());
}

#[test]
fn duplicate_opening_indices_and_noncanonical_frontiers_reject() {
    let context = Digest::default();
    let leaves = [Digest { data: [1; 32] }, Digest { data: [2; 32] }];
    let tree = MerkleHeap::new(&context, &leaves);
    let path = tree.generate_proof(&[0, 1]);
    let opened = [(0, leaves[0]), (1, leaves[1])];
    assert!(verify_proof(&context, 2, &tree.root(), &path, &opened).is_ok());
    assert_eq!(
        verify_proof(
            &context,
            2,
            &tree.root(),
            &path,
            &[(0, leaves[0]), (0, leaves[0])]
        ),
        Err(MerkleError::DuplicateLeafIndex { index: 0 })
    );
    assert!(verify_proof(&context, 2, &tree.root(), &[leaves[0]], &opened).is_err());
    assert!(verify_proof(&context, 2, &tree.root(), &[], &[(0, leaves[0])]).is_err());
}
