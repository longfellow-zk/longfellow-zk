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

//! Fixed Merkle heap with leaves at `n..2*n` and parents below `n`.
//! Traversal and proof order also cover non-power-of-two leaf counts.
//! Node hashing is supplied by the v2 authentication codec in `hash`.

use super::{Digest, MerkleError};

/// Returns a mask indicating which nodes in the heap lie on the path
/// from the requested leaves (`leaf_indices`) to the root.
fn mark_paths_to_root(num_leaves: usize, leaf_indices: &[usize]) -> Result<Vec<bool>, MerkleError> {
    if leaf_indices.is_empty() {
        return Err(MerkleError::EmptyLeaves);
    }
    let mut is_node_on_path = vec![false; 2 * num_leaves];
    for &leaf_idx in leaf_indices {
        if leaf_idx >= num_leaves {
            return Err(MerkleError::LeafIndexOutOfBounds {
                index: leaf_idx,
                num_leaves,
            });
        }
        let heap_idx = leaf_idx + num_leaves;
        if is_node_on_path[heap_idx] {
            return Err(MerkleError::DuplicateLeafIndex { index: leaf_idx });
        }
        is_node_on_path[heap_idx] = true;
    }
    for i in (1..num_leaves).rev() {
        is_node_on_path[i] = is_node_on_path[2 * i] || is_node_on_path[2 * i + 1];
    }
    if !is_node_on_path[1] {
        return Err(MerkleError::LeafIndexNotOnPath);
    }
    Ok(is_node_on_path)
}

/// Representation of a built, immutable Merkle heap.
#[cfg(any(test, feature = "prover"))]
#[derive(Clone)]
pub(in crate::runtime::v2) struct MerkleHeap {
    num_leaves: usize,
    layers: Vec<Digest>,
}

#[cfg(any(test, feature = "prover"))]
impl MerkleHeap {
    /// Build the same fixed heap with a caller-selected internal-node codec.
    pub(in crate::runtime::v2) fn new_with_hash(
        leaves: &[Digest],
        hash: impl Fn(&Digest, &Digest) -> Digest,
    ) -> Self {
        let num_leaves = leaves.len();
        assert!(num_leaves > 0, "Cannot construct an empty Merkle heap");
        let mut layers = vec![Digest::default(); 2 * num_leaves];

        // Copy leaves
        layers[num_leaves..2 * num_leaves].copy_from_slice(leaves);

        // Build parent nodes bottom-up
        for i in (1..num_leaves).rev() {
            layers[i] = hash(&layers[2 * i], &layers[2 * i + 1]);
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

/// Verifies that the opened leaf digests match the commitment root.
///
/// Geometry fixes every leaf position. Opened indices must be distinct and
/// in range, and the supplied frontier must be consumed exactly. The caller
/// supplies the domain-separated node hash from the v2 authentication codec.
#[cfg(any(test, feature = "verifier"))]
pub(in crate::runtime::v2) fn verify_proof_with_hash(
    num_leaves: usize,
    root: &Digest,
    proof: &[Digest],
    leaves: &[(usize, Digest)],
    hash: impl Fn(&Digest, &Digest) -> Digest,
) -> Result<(), MerkleError> {
    let leaf_indices: Vec<usize> = leaves.iter().map(|(idx, _)| *idx).collect();
    // `None` means this node has not been supplied or derived.  Do not use a
    // sentinel digest here: an all-zero digest is valid proof data and must
    // never be confused with an uncomputed node.
    let mut computed_nodes = vec![None; 2 * num_leaves];

    let is_node_on_path = mark_paths_to_root(num_leaves, &leaf_indices)?;
    let mut proof_idx = 0;

    // 1. Populate sibling nodes from the proof path
    for i in (1..num_leaves).rev() {
        if is_node_on_path[i] {
            if is_node_on_path[2 * i] && !is_node_on_path[2 * i + 1] {
                if proof_idx >= proof.len() {
                    return Err(MerkleError::ProofLengthMismatch {
                        expected: proof_idx + 1,
                        found: proof.len(),
                    });
                }
                computed_nodes[2 * i + 1] = Some(proof[proof_idx]);
                proof_idx += 1;
            } else if !is_node_on_path[2 * i] && is_node_on_path[2 * i + 1] {
                if proof_idx >= proof.len() {
                    return Err(MerkleError::ProofLengthMismatch {
                        expected: proof_idx + 1,
                        found: proof.len(),
                    });
                }
                computed_nodes[2 * i] = Some(proof[proof_idx]);
                proof_idx += 1;
            }
        }
    }

    // A valid multi-proof has exactly the sibling nodes requested by the
    // traversal.  Reject trailing entries rather than silently accepting a
    // second encoding of the same opening.
    if proof_idx != proof.len() {
        return Err(MerkleError::ProofLengthMismatch {
            expected: proof_idx,
            found: proof.len(),
        });
    }

    // 2. Populate the opened leaves
    for &(leaf_idx, leaf_digest) in leaves {
        let heap_idx = leaf_idx + num_leaves;
        computed_nodes[heap_idx] = Some(leaf_digest);
    }

    // 3. Reconstruct internal nodes bottom-up
    for i in (1..num_leaves).rev() {
        if let (Some(left), Some(right)) = (computed_nodes[2 * i], computed_nodes[2 * i + 1]) {
            computed_nodes[i] = Some(hash(&left, &right));
        }
    }

    let computed_root = computed_nodes[1].ok_or(MerkleError::RootMismatch {
        expected: *root,
        found: Digest::default(),
    })?;
    if root != &computed_root {
        return Err(MerkleError::RootMismatch {
            expected: *root,
            found: computed_root,
        });
    }
    Ok(())
}
