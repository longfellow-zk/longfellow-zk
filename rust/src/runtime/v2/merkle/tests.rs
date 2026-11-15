// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use sha2::Digest as _;

use super::{heap::MerkleError, *};
use crate::runtime::v2::proto::{Digest, MerkleNonce, NONCE_LEN};

#[test]
fn codecs_bind_role_index_and_salt() {
    let zero = Digest::default();
    let other = Digest { data: [1; 32] };
    let salt = MerkleNonce {
        bytes: [7; NONCE_LEN],
    };
    let leaf = |index, salt: &_| {
        let mut h = hash::leaf(index, salt);
        h.update(1u128.to_le_bytes());
        Digest {
            data: h.finalize().into(),
        }
    };
    let digest = leaf(0, &salt);
    assert_ne!(digest, leaf(1, &salt));
    let mut changed_salt = salt;
    changed_salt.bytes[0] ^= 1;
    assert_ne!(digest, leaf(0, &changed_salt));
    changed_salt = salt;
    changed_salt.bytes[NONCE_LEN - 1] ^= 1;
    assert_ne!(digest, leaf(0, &changed_salt));
    assert_ne!(digest, hash::node(1, &zero, &other));
    let node = hash::node(1, &digest, &other);
    assert_ne!(node, hash::node(2, &digest, &other));
    assert_ne!(node, hash::node(1, &other, &digest));
}

/// The Merkle hash domain is the documented label, zero-padded to the
/// 32-byte width of a digest.
#[test]
fn domain_is_the_padded_label() {
    let label = b"longfellow/v2/merkle/domain";
    assert_eq!(&hash::DOMAIN[..label.len()], label);
    assert!(hash::DOMAIN[label.len()..].iter().all(|&b| b == 0));
}

#[test]
fn independent_node_vector_binds_little_endian_u64_index() {
    // Generated independently with printf and coreutils sha256sum over
    // "polygero/joint/node/v1" || DOMAIN || LE64(index) || [11; 32] || [13; 32].
    let digest = hash::node(
        0x01020304,
        &Digest { data: [11; 32] },
        &Digest { data: [13; 32] },
    );
    assert_eq!(
        hex::encode(digest.data),
        "57fd386f72560980c73d88648c0a04f18243272283120511a62e71173247891d"
    );
}

/// Hash a leaf at position `j` with a fixed salt and column bytes.
fn leaf_vector(j: usize) -> String {
    let mut h = hash::leaf(
        j,
        &MerkleNonce {
            bytes: [9; NONCE_LEN],
        },
    );
    h.update([0xaa; 16]);
    h.update([0xbb; 32]);
    hex::encode(h.finalize())
}

// Both vectors were generated independently with printf and coreutils
// sha256sum over "polygero/joint/leaf/v1" || DOMAIN || LE64(j) || [9; 32]
// followed by caller-appended column bytes [0xaa; 16] || [0xbb; 32].

#[test]
fn independent_leaf_vector_pins_preimage_layout() {
    assert_eq!(
        leaf_vector(0x01020304),
        "506682505638232b18b7666d20cb15b510f5c247776924420f70b147b0d94e38"
    );
}

/// A position above 2^32 checks that all eight bytes of the position are hashed.
#[cfg(target_pointer_width = "64")]
#[test]
fn independent_leaf_vector_pins_all_position_bytes() {
    assert_eq!(
        leaf_vector(0x0102030405),
        "bf393c4c51d91e305843911a00e5d7625c1406e3ddd1007009467e39c4f897cc"
    );
}

#[test]
fn indexed_heaps_support_unbalanced_trees_and_unsorted_openings() {
    // Identical digests deliberately exercise position binding without relying
    // on the leaf codec to distinguish the subtrees for us.
    for n in [1, 2, 3, 5, 8, 17] {
        let leaves = vec![Digest { data: [7; 32] }; n];
        let tree = MerkleHeap::new(&leaves);
        for indices in [vec![0], vec![n - 1], (0..n).rev().collect()] {
            let path = tree.generate_proof(&indices);
            let opened: Vec<_> = indices.iter().map(|&i| (i, leaves[i])).collect();
            assert!(verify_proof(n, &tree.root(), &path, &opened).is_ok());
        }
    }
}

#[test]
fn internal_nodes_cannot_be_moved_to_another_heap_position() {
    let leaf = Digest { data: [7; 32] };
    let left = hash::node(2, &leaf, &leaf);
    let right = hash::node(3, &leaf, &leaf);
    assert_ne!(left, right);
    let tree = MerkleHeap::new(&[leaf; 4]);
    assert_eq!(tree.root(), hash::node(1, &left, &right));
    let path = tree.generate_proof(&[0, 1]);
    assert_eq!(path, vec![right]);
    assert!(verify_proof(4, &tree.root(), &path, &[(0, leaf), (1, leaf)]).is_ok());
    assert!(verify_proof(4, &tree.root(), &[left], &[(0, leaf), (1, leaf)]).is_err());
}

#[test]
fn duplicate_opening_indices_and_noncanonical_frontiers_reject() {
    let leaves = [Digest { data: [1; 32] }, Digest { data: [2; 32] }];
    let tree = MerkleHeap::new(&leaves);
    let path = tree.generate_proof(&[0, 1]);
    let opened = [(0, leaves[0]), (1, leaves[1])];
    assert!(verify_proof(2, &tree.root(), &path, &opened).is_ok());
    assert_eq!(
        verify_proof(2, &tree.root(), &path, &[(0, leaves[0]), (0, leaves[0])]),
        Err(MerkleError::DuplicateLeafIndex { index: 0 })
    );
    assert!(verify_proof(2, &tree.root(), &[leaves[0]], &opened).is_err());
    assert!(verify_proof(2, &tree.root(), &[], &[(0, leaves[0])]).is_err());
}

#[test]
fn verification_rejects_leaf_indices_at_or_beyond_the_leaf_count() {
    // Indices in [n, 2n) address internal heap slots, not leaves. Verification
    // must reject them before indexing, even though sampling never produces them.
    let root = Digest { data: [5; 32] };
    let leaf = Digest { data: [7; 32] };
    for index in [5, 9, 10, usize::MAX] {
        let result = verify_proof(5, &root, &[], &[(index, leaf)]);
        assert!(
            matches!(
                result,
                Err(MerkleError::LeafIndexOutOfBounds { index: i, num_leaves: 5 }) if i == index
            ),
            "leaf index {index}"
        );
    }
}
