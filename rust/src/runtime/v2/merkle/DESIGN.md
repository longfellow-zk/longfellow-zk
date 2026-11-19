# Merkle commitment design

The v2 Merkle commitment authenticates the columns of the joint Polygero
oracle. It is a salted SHA-256 tree over `n` leaves in a fixed binary heap,
with every hash bound to a fixed domain and to its position. It is field
independent: a leaf commits to a byte string that the caller appends, and
the tree sees only digests. Joint Polygero is its only user
(`runtime/v2/polygero/DESIGN.md`): Polygero builds one leaf per column from
every field's row values, sends the root as its `Commitment` message, and
after the query draw opens the queried columns with their nonces and one
shared frontier. The Merkle module never touches the transcript.

Code comments and other design documents cite the invariants below as
"Merkle I1" and so on.

## Statement

**Commit.** Input: `n >= 1` leaf messages of one fixed
width, and `n` independent 32-byte nonces. Output: a 32-byte root.

**Open.** Input: a list `I` of distinct leaf indices in `0..n`. Output: the
nonces of `I` in the caller's order and the frontier: the digests of the
nodes that are siblings of a path node and not on any path, in decreasing
heap index.

**Verify.** Input: `n`, the root, the frontier, and one
`(index, leaf digest)` pair per opened leaf. The verifier accepts if and only
if the root it recomputes from exactly these values equals the given root.
Binding: an accepted opening reveals the leaf messages fixed at commitment,
except for the hash events below. Hiding: unopened leaves reveal nothing
about their messages, except for the hiding error below.

## Invariants

**I1. Leaf and node preimages are disjoint and injective.** A leaf preimage
starts with the 22-byte tag `polygero/joint/leaf/v1`, a node preimage with
the 22-byte tag `polygero/joint/node/v1`. Every following field has a fixed
width, and the caller's leaf message has a width fixed by the geometry, so
each preimage parses in exactly one way.
*Enforced by:* `hash::leaf` and `hash::node` are the only preimage writers;
the pinned vectors `independent_leaf_vector_pins_preimage_layout` and
`independent_node_vector_binds_little_endian_u64_index`;
`LfzkV2.Current.MerkleWireCodec.codec_inj` and `domains_ne`.

**I2. Every hash binds its position.** A leaf binds its leaf index `j` in
`0..n`; a node binds its heap index `i` in `1..n`. The position comes from
the heap traversal, never from the proof, so a digest cannot be moved to
another position even when two subtrees have equal digests.
*Enforced by:* `hash::node` takes the index and only the traversals in
`prover.rs` and `verifier.rs` call it (type, visibility); the test
`internal_nodes_cannot_be_moved_to_another_heap_position`;
`Merkle.Indexed.RoleDecoders`, whose node decoder checks the expected index,
and `Merkle.Indexed.Independence`.

**I3. Every hash carries the fixed domain.** Both preimages carry, after their
role tag, the 32-byte protocol constant `DOMAIN`
(`DOMAIN` (`runtime/v2/merkle/hash.rs`)): the label `longfellow/v2/merkle/domain`
zero-padded to 32 bytes. The parameters that fix the tree's shape and the
leaf layout are bound by the transcript statement, not by the hash inputs
(transcript I3); the evaluation domain is fixed by the verifier and bound
nowhere. The domain is neither absorbed nor sent (transcript I11).
*Enforced by:* `hash::leaf` and `hash::node` write `DOMAIN` themselves and
take no domain argument (type); the tests `domain_is_the_padded_label` and
`codecs_bind_role_index_and_salt`.

**I4. Merkle inputs are disjoint from transcript inputs.** Every Merkle
preimage starts with ASCII `p` (112); strand nodes and PRF blocks start with
`u32` values 1 and 0. A Merkle query can never answer a transcript query, or
the reverse.
*Enforced by:* `LfzkV2.Current.StrandMerkleDomains` (`input_ne_leaf`,
`input_ne_node`), a syntax fact needing no collision resistance.

**I5. One fresh nonce per leaf.** Each of the `n` leaves gets its own 32-byte
nonce from the prover's private randomness. Nonces are not derived from the
transcript, the domain or each other.
*Enforced by:* `ColumnOracle::new` fills each of the `n` nonces from its
`PrivateRandom` (type); `MerkleNonce` holds exactly `[u8; NONCE_LEN]`.

**I6. The heap shape is a function of `n` alone.** Leaves sit at heap
positions `n..2n`, internal nodes at `1..n`, node `i` has children `2i` and
`2i+1`, and the root is position 1. This holds for every `n >= 1`, powers of
two or not. The verifier takes `n` from the absorbed geometry, never from the
proof (transcript I2).
*Enforced by:* `MerkleHeap::new` builds the heap for `n`, and
`MerkleHeap::generate_proof` and `verify_proof` share `mark_paths_to_root`
(runtime); the test
`indexed_heaps_support_unbalanced_trees_and_unsorted_openings`; `Merkle.Heap`.

**I7. Each opening has exactly one frontier.** The frontier is the set of
non-path siblings of path nodes, in decreasing heap index. The verifier
consumes it exactly: a missing or extra digest rejects, so no opening has a
second encoding.
*Enforced by:* `generate_proof` and `verify_proof` take each frontier
position from one helper, `frontier_child` (`heap.rs`); `verify_proof`
returns `OpeningError::ProofLengthMismatch` unless the
traversal consumes every frontier digest (runtime); the test
`duplicate_opening_indices_and_noncanonical_frontiers_reject`;
`Heap.frontier`.

**I8. Opened indices are distinct and in range.** The verifier rejects an
empty list, a repeated index or an index `>= n` before it indexes the heap
or the path mask with it. Both arrays are sized from the trusted geometry
before the check.
*Enforced by:* `mark_paths_to_root` (runtime); the test
`verification_rejects_leaf_indices_at_or_beyond_the_leaf_count`.

## Heap layout

The heap is an array of `2n` digests; position 0 is unused. Leaf `j` is at
position `n+j`, so leaves of a non-power-of-two heap sit at two depths. The
depth of the heap is `floor(log2(2n-1)) = ceil(log2 n)` (`Heap.heapDepth`),
so one opened leaf contributes at most `ceil(log2 n)` frontier digests. For
`n = 1` the root is the leaf digest itself. Example, `n = 5`:

| Position | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|
| Content | root | node | node | node | leaf 0 | leaf 1 | leaf 2 | leaf 3 | leaf 4 |
| Children | 2, 3 | 4, 5 | 6, 7 | 8, 9 | | | | | |

Opening leaf 0 (position 5): the path is 5, 2, 1, and the frontier is
position 4 (sibling of 5), then position 3 (sibling of 2).

## Protocol

The Merkle commitment has no transcript messages of its own. Its values
travel inside Polygero's schedule:

| Value | Sent where | Absorbed |
|---|---|---|
| root | Polygero `Commitment` (tag 32), Bytes(32) | yes, when sent |
| nonces of the opened leaves | Polygero terminal data, query order | only by the seal (transcript I4) |
| frontier count and frontier | Polygero terminal data, the end of the body | only by the seal (transcript I4) |

**Commit** (`MerkleHeap::new`): copy the `n` leaf digests to positions
`n..2n`; for `i` from `n-1` down to 1, set
`heap[i] = node(i, heap[2i], heap[2i+1])`.

**Open** (`MerkleHeap::generate_proof`): mark the path of every opened leaf.
For `i` from `n-1` down to 1, if `i` is on a path and exactly one child is,
append the other child's digest.

**Verify** (`verify_proof`):

1. Mark the paths; reject an empty, repeated or out-of-range index (I8).
2. For `i` from `n-1` down to 1, where `i` is on a path and exactly one child
   is, take the next frontier digest as the other child; reject if the
   frontier runs out.
3. Reject if any frontier digest is left over (I7).
4. Place the opened leaf digests at their positions.
5. For `i` from `n-1` down to 1, hash every node whose two children are known,
   with its own index (I2). Unknown nodes are `None`, never a sentinel
   digest, since an all-zero digest is valid proof data.
6. Accept if and only if the recomputed root equals the given root.

Each path node is hashed exactly once; the verifier hashes `|I|` leaves and
the internal path nodes.

## Formats

All integers are u64 little endian. A digest is 32 bytes.

**Leaf preimage** (`hash::leaf`, then the caller appends the message):

| Offset | Bytes | Field |
|---|---|---|
| 0 | 22 | ASCII `polygero/joint/leaf/v1` |
| 22 | 32 | `DOMAIN` |
| 54 | 8 | `u64(j)`, leaf index in `0..n` |
| 62 | 32 | nonce of leaf `j` |
| 94 | `w` | leaf message, `w` fixed by the geometry |

For Polygero the message is column `j`: for each participant in tuple order,
for each row in row order, the canonical encoding of that row's value at the
column. Leaf digest: `SHA256(preimage)`.

**Node preimage** (`hash::node`), 126 bytes:

| Offset | Bytes | Field |
|---|---|---|
| 0 | 22 | ASCII `polygero/joint/node/v1` |
| 22 | 32 | `DOMAIN` |
| 54 | 8 | `u64(i)`, heap index in `1..n` |
| 62 | 32 | left child digest, position `2i` |
| 94 | 32 | right child digest, position `2i+1` |

**Opening on the wire** (`MerkleProof`, the last terminal fields of the proof
body, after the Polygero rows):

```text
opening  := nonce{t} frontier   ; t = number of opened leaves, from the geometry
nonce    := byte{32}            ; in query order
frontier := u64(f) digest{f}    ; the last field of the body, decreasing heap index
```

The nonce count comes from the geometry; the frontier states its digest
count `f` in one u64 word. Before parsing, the complete reader checks once
that the proof has exactly the length the geometry and `f` determine, with
`f <= t*(ceil(log2 n)+1)` (proto I3). `MerkleProof::read_path` reads the
count, which may not exceed that capacity, and exactly that many digests;
`JointPolygeroProof::read` requires that nothing follow them, and
`verify_proof` then requires the exact canonical count (I7).

## Rust API

```rust
// runtime::v2::proto (the prover/verifier contract)
pub struct Digest { pub data: [u8; 32] }
pub const NONCE_LEN: usize = 32;
pub(in crate::runtime::v2) struct MerkleNonce { pub(in crate::runtime::v2) bytes: [u8; NONCE_LEN] }  // Debug omits the bytes
pub(in crate::runtime::v2) struct MerkleProof {
    pub(in crate::runtime::v2) nonce: Vec<MerkleNonce>,  // query order
    pub(in crate::runtime::v2) path: Vec<Digest>,        // the frontier, decreasing heap index
}
impl MerkleProof {                                       // the opening codec
    pub(in crate::runtime::v2) fn write_nonces(&self, buf: &mut Vec<u8>);
    pub(in crate::runtime::v2) fn read_nonces(bytes: &mut &[u8], num_queries: usize)
        -> Result<Vec<MerkleNonce>, std::io::Error>;
    pub(in crate::runtime::v2) fn write_path(&self, buf: &mut Vec<u8>);  // u64 count, then digests
    // max_sz: the opening's checked frontier capacity (Polygero's opening shape check)
    pub(in crate::runtime::v2) fn read_path(bytes: &mut &[u8], max_sz: usize)
        -> Result<Vec<Digest>, std::io::Error>;  // count <= max_sz
}

// runtime::v2::merkle
pub(in crate::runtime::v2) mod hash {
    pub(super) const DOMAIN: [u8; 32] = *b"longfellow/v2/merkle/domain\0\0\0\0\0";  // I3
    // I1, I2, I3: the leaf header; the caller appends the fixed-width message.
    pub(in crate::runtime::v2) fn leaf(j: usize, salt: &MerkleNonce) -> Sha256;
    // I2: called only by the heap traversals, with the traversal's index.
    pub(super) fn node(index: usize, l: &Digest, r: &Digest) -> Digest;
}
pub(in crate::runtime::v2) struct MerkleHeap { /* num_leaves, layers: 2n digests */ }
impl MerkleHeap {                                          // prover.rs
    pub(in crate::runtime::v2) fn new(leaves: &[Digest]) -> Self;
    pub(in crate::runtime::v2) fn root(&self) -> Digest;
    pub(in crate::runtime::v2) fn generate_proof(&self, leaf_indices: &[usize]) -> Vec<Digest>;
}
pub(in crate::runtime::v2) fn verify_proof(                // verifier.rs
    num_leaves: usize,                                     // I6: from the absorbed geometry
    root: &Digest,
    proof: &[Digest],                                      // the frontier
    leaves: &[(usize, Digest)],                            // (leaf index, leaf digest), any order
) -> Result<(), OpeningError>;
pub(in crate::runtime::v2) enum MerkleError {             // heap.rs: both roles
    DuplicateLeafIndex { index: usize },
    LeafIndexOutOfBounds { index: usize, num_leaves: usize },
    EmptyLeaves,
}
pub(in crate::runtime::v2) enum OpeningError {             // verifier.rs
    Paths(MerkleError),
    ProofLengthMismatch { expected: usize, found: usize },
    RootMismatch { expected: Digest, found: Digest },
}
```

`MerkleHeap` (`prover.rs`) is built under the `prover` feature and
`verify_proof` (`verifier.rs`) under the `verifier` feature; neither role
links the other's code, and both share the path marking of `heap.rs`. Leaf indices passed
to `generate_proof` come from the transcript's `indices` draw
(`Reading::choose`), which yields distinct indices in range, so a violation
is a prover bug and panics.
`verify_proof` takes untrusted indices and returns an error instead.

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| A node digest presented as a leaf, or the reverse | I1: distinct tags |
| A subtree moved to another heap position | I2: node hashes bind their index from the traversal |
| A leaf opened at another column | I2: the leaf hash binds `j` |
| A root reused under another geometry | transcript I3: the statement binds the geometry before the root is sent |
| A Merkle query answering a transcript query | I4: first-byte separation |
| Two columns linked by a shared or predictable nonce | I5: one private nonce per leaf |
| A proof that chooses the tree size | I6: `n` comes from the geometry |
| Two encodings of one opening (trailing or missing digests) | I7: exact frontier consumption |
| An index at or beyond `n` addressing an internal heap slot | I8: bounds check before indexing |
| An opened leaf listed twice | I8: duplicate check |
| An all-zero digest mistaken for an uncomputed node | verification uses `Option<Digest>` |
| An oversized frontier forcing allocation | the one length check, with the frontier count capped, before parsing |

## Soundness and zero knowledge

**Binding and extraction.** The extractor reads every column from the
original hash-query table at the commitment cut, following each leaf's heap
ancestors from the root (`Merkle.Indexed.Extraction`, `column_eq_opened`).
Position binding (I2) lets it decode each node input against the expected
index, so a node from another position cannot be grafted in
(`Merkle.Indexed.Codec`, `Merkle.Indexed.Independence`). An accepted
opening then agrees with the extracted columns unless a hash event occurs:
a collision among the adversary's `Q` original queries, charged
`Q(Q-1)/(2*2^256)`, or a fresh query hitting one label on one indexed path
(`Merkle.FreshHit`, `LfzkV2.Current.StrandMerkleBounds`). Both are part of
the end-to-end correction `(choose(Q, 2) + r + 15)/2^256` in
`formal/README.md`. The verifier's own authentication queries do not enlarge
the adversary's budget.

**Hiding.** Leaf `j`'s hash input contains a fresh 256-bit nonce (I5). In
the ghost experiment, independent leaf labels replace the salted leaf hashes;
the distance between real and ghost views is at most
`(Q_pre + Q_post)/2^256` over the observer's raw calls before and after the
proof
(`LfzkV2.Current.ZeroKnowledge.StrandCanonicalCommitmentHiding.commitment_hiding`,
`Merkle.Hiding`). Nonces are not assumed collision-free. This is the only
statistical term of `Mdoc.ZeroKnowledge.statClose`.

**Codec.** `LfzkV2.Current.MerkleWireCodec` defines the leaf and node
preimages byte for byte as above and proves them injective (`codec_inj`) with
executable decoders; `StrandMerkleDomains` separates them from the transcript.

## Open questions

None.
