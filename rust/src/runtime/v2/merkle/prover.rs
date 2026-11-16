// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's heap: built once from the leaves, it opens any set of them.
use super::{hash, heap::mark_paths_to_root};
use crate::runtime::v2::proto::Digest;

/// Representation of a built, immutable Merkle heap.
#[derive(Clone)]
pub(in crate::runtime::v2) struct MerkleHeap {
    num_leaves: usize,
    layers: Vec<Digest>,
}

impl MerkleHeap {
    /// Build the fixed heap, binding every internal node to its position.
    pub(in crate::runtime::v2) fn new(leaves: &[Digest]) -> Self {
        let num_leaves = leaves.len();
        assert!(num_leaves > 0, "Cannot construct an empty Merkle heap");
        let mut layers = vec![Digest::default(); 2 * num_leaves];

        // Copy leaves
        layers[num_leaves..2 * num_leaves].copy_from_slice(leaves);

        // Build parent nodes bottom-up
        for i in (1..num_leaves).rev() {
            layers[i] = hash::node(i, &layers[2 * i], &layers[2 * i + 1]);
        }

        Self { num_leaves, layers }
    }

    /// Returns the root digest of the Merkle heap.
    #[must_use]
    pub(in crate::runtime::v2) fn root(&self) -> Digest {
        self.layers[1]
    }

    /// Generates a multi-leaf opening proof for the queried leaf positions.
    #[must_use]
    pub(in crate::runtime::v2) fn generate_proof(&self, leaf_indices: &[usize]) -> Vec<Digest> {
        let is_node_on_path = mark_paths_to_root(self.num_leaves, leaf_indices)
            .expect("Invalid leaf indices for proof generation");
        let mut proof = Vec::new();

        // Traverse internal nodes from bottom to top
        for i in (1..self.num_leaves).rev() {
            if is_node_on_path[i] {
                // If only one of the children is on the path, the other child's
                // digest must be included in the proof so the
                // verifier can compute the parent digest.
                if is_node_on_path[2 * i] && !is_node_on_path[2 * i + 1] {
                    proof.push(self.layers[2 * i + 1]);
                } else if !is_node_on_path[2 * i] && is_node_on_path[2 * i + 1] {
                    proof.push(self.layers[2 * i]);
                }
            }
        }
        proof
    }
}
