# Experimental formal circuit commitment (LFC3)

Status: implemented for experimentation. It is not yet selected by the mdoc
prover or verifier.

## Decision

The verifier pins one 32-byte SHA-256 page-Merkle root of the exact,
uncompressed LFC3 circuit payload. It verifies that root before decoding and
rejects trailing bytes. The old expanded `compute_id` is retained in the LFC3
trailer only for compatibility with the current Rust `Circuit` type; it is not
the formal binding check.

LFC3 is LFC2 plus a bounded second dictionary over each layer's segment-token
stream. A token phrase contains at most 16 segment indices. A layer uses the
phrase encoding only when its exact ULEB128 wire size is smaller than its flat
token encoding. This captures the repeated SHA-256 bodies without a recursive
grammar or a zstd decoder in the trusted formal path.

## Canonical payload

Every integer below is the unique shortest ULEB128 representation of a value
at most `0x0fffffff`. The reader rejects overlong representations. Field
elements have the fixed canonical byte representation of the selected field.

```text
"LFC3"
field_id, noutput, 1, npublic_input, subfield_boundary, ninput, layer_count
constant_count, constants[constant_count]

for each layer:
  logw, nw
  delta_count
  (zigzag(g), zigzag(h0), zigzag(h1), constant_index)[delta_count]
  segment_count
  (segment_length, delta_index[segment_length])[segment_count]
  token_encoding
  if token_encoding = 0:
    token_count, segment_index[token_count]
  if token_encoding = 1:
    phrase_count
    (phrase_length, segment_index[phrase_length])[phrase_count]
    root_count, phrase_index[root_count]

legacy_circuit_id[32]
```

Phrase expansion has exactly one extra level:

```text
root phrase index -> phrase of segment indices -> segment of delta indices
```

There are no recursive rules or forward references. The Rust reader bounds
the size of each dictionary and both expanded token and term counts before it
constructs a circuit.

## Commitment

The page size is 4096 bytes. Integer fields in hash inputs are fixed-width
little-endian.

```text
leaf(i) = SHA256(
  "LFZK-LFC-PAGE-V1\0" ||
  payload_byte_length:u64 || page_index:u64 || page_length:u32 || page_bytes)

node(level, left, right) = SHA256(
  "LFZK-LFC-NODE-V1\0" || level:u32 || left[32] || right[32])

root = SHA256(
  "LFZK-LFC-ROOT-V1\0" || 4096:u32 ||
  payload_byte_length:u64 || page_count:u64 || tree_root[32])
```

An empty payload has one empty page. At each tree level an odd final digest is
paired with itself. The root envelope commits to the byte length and leaf
count, so this padding convention cannot alias a payload with a different
number of pages without a SHA-256 collision.

The root is a computational commitment, not an unconditional proof of byte
equality. Security depends on SHA-256 collision/second-preimage resistance.
Domain separation and committed lengths make the reduction to that assumption
straightforward and avoid leaf/node or parsing-boundary ambiguity.

## Lean ingestion

`Sha256.lean` is a kernel-reducible SHA-256 implementation using `Nat`, lists,
and total fuelled loops. `CircuitCommitment.lean` mirrors the Rust page tree and
provides `packedLeafHash`. A generated page module can contain:

```lean
set_option maxHeartbeats 0
def packed : Nat := <one little-endian 4096-byte integer>
theorem page_ok :
    packedLeafHash totalLength pageIndex pageLength packed = expected := by
  decide
```

Thus the bytes occur as one packed natural per page, not as millions of Lean
array elements, and no elaborator reads an external file. Page theorems are
independent and can be built in parallel. The small root module imports their
32-byte results and checks only the Merkle tree.

`Lfc3.lean` now consumes those same packed naturals directly. It checks the
magic, shortest ULEB28 encodings, field identity and canonical fixed-width
field elements, all resource bounds and dictionary indices, the bounded
phrase expansion, wrapping 32-bit deltas, and exact end of input. It produces
`DecodedCircuit`, whose `toRaw` operation takes only DAG/wiring/assertion/layout
advice. Dimensions, constants and expanded layers can therefore come only
from the committed artifact.

The checked-in Rung1 path demonstrates the full composition:

- `Rung1ArtifactPacked0.lean` contains the 297 LFC3 bytes as one packed `Nat`;
- `Rung1ArtifactCommitment*.lean` proves their page leaf and root;
- `Rung1Artifact.decode_ok` proves the verified decoder succeeds;
- `Rung1Data.artifactRaw_eq_raw` proves the decoded `RawCircuit` equals the
  compact generated cache used by the existing structural proof; and
- `Rung1.accepts_artifact_iff_spec` proves `Accepts` for the decoded circuit is
  equivalent to the handwritten elliptic-curve specification, using constants
  decoded from the bytes.

`rust/core/proto/examples/lfc3_to_lean.rs` emits the packed page, leaf and root
modules. `rust/circuits/ec/examples/rung1_lfc2.rs` reproduces the Rung1 source
artifact.

The Rust and Lean implementations share roots for the empty payload and
`abc` test vectors:

```text
empty  6662ec67ad6672b605c1e656312ab3c936d3ef7342cd0571af80a27648c1aa37
abc    187ab7e247371c594ffe6fbf4df6c6a56defbd293c43ac65fe86c703ca9ab9e0
```

## mdoc experiment

The checked-in v7 four-attribute artifact
`5aebdaaafe17296a3ef3ca6c80c6e7505e09291897c39700410a365fb278e460`
was decoded and re-encoded without changing prover/verifier selection.

| circuit | terms | LFC2 bytes | LFC3 bytes | LFC3/LFC2 | 4 KiB pages |
|---|---:|---:|---:|---:|---:|
| signature | 481,833 | 478,823 | 476,346 | 99.48% | 117 |
| hash (40 SHA copies plus attribute work) | 9,063,890 | 1,419,484 | 1,173,100 | 82.64% | 287 |

In an optimized local run, LFC3 writing / root computation / committed decode
took 3.57 ms / 0.20 ms / 1.17 ms for the signature circuit and 19.24 ms /
0.48 ms / 2.96 ms for the hash circuit. The new runtime check is therefore
negligible compared with proof verification; the cost is in kernel evaluation
of the generated Lean page theorems.

For the hash circuit, 284,675 LFC2 segment tokens became a phrase dictionary
with 63,635 symbols and 18,130 root references. Phrase sizes 16, 32, 64, 128,
and 256 were tested; 16 had the smallest exact wire encoding. Two alternatives
were also rejected empirically:

- Global cross-layer dictionaries saved only 1,277 of 62,665 delta entries and
  63 of 15,800 segments; their wider indices made the grammar larger.
- Fixed-width bit packing was 10.58% larger for the hash circuit and 11.92%
  larger for the signature circuit than frequency-sorted ULEB128.

The other three v7 hash variants give the same result: LFC3 is 81.96%, 82.54%,
and 82.80% of LFC2 (237, 254, and 278 pages), and a 16-token phrase is smaller
than 32 tokens in every case. The choice is therefore not specific to the
largest artifact.

zstd sizes are slightly worse for LFC3 (366,200 versus 350,799 bytes for the
hash payload), because zstd already exploits repeated token runs. That is not
the relevant formal metric: hashing zstd bytes would require trusting or
verifying the zstd decoder. The uncompressed canonical LFC3 payload is what the
verified decoder consumes and what the root commits to.

At the previously measured roughly 24 seconds of kernel CPU per 4 KiB page,
the two LFC3 payloads require 404 independent page checks instead of 464 for
LFC2, about 2.7 CPU-hours before the roughly 5% Merkle-node overhead. This is
appropriate for parallel generated modules, but it is still expensive; a
single serial Lean build is not the intended execution model.

The production `packedLeafHash` path was also measured directly on a full
4096-byte deterministic page: 23.12 seconds of user CPU and 25.99 seconds wall.
The SHA schedule is maintained newest-first so both insertion and the four
schedule lookups are constant-position list operations during reduction.

## Decoder scaling experiment

The byte representation is no longer the limiting factor. A monolithic
reduction that both parses and materialises a large flat `List RawTerm` is.
The initial kernel-only measurements (no `native_decide`) were:

| input | LFC3 bytes | expanded terms | decoder check |
|---|---:|---:|---:|
| Rung1 | 297 | 17 | 0.43 s for the decode module |
| first 10 SHA layers | 8,968 | 12,319 | 42.85 s |
| full SHA test circuit | 28,328 | 79,093 | did not finish in 137 s (`decide`) or 365 s (`rfl`) |

This validates the direct path for moderate circuits around ten thousand
terms and rejects a single whole-circuit reduction for larger inputs.

That next scaling step is now implemented. `Lfc3.lean` exposes resumable term
expansion and staged header/layer/trailer parsing. `lfc3_to_lean` emits:

- explicit parser cursors at every layer boundary;
- one independently checked compact-layer cache per layer;
- fixed-size `RawTerm` chunks and their expansion start/stop cursors;
- opaque generic compositions for chunks, layers, the staged parser, and the
  final `decode = .ok decoded` theorem.

The opacity of composition is load-bearing. A `simp`-based 12-layer
composition accidentally unfolded the 79,093-term payload and ran for more
than six minutes. `LayersExpand`, `LayerParseSteps`, and
`decode_eq_of_compressed` reduce the corresponding top modules to 0.22--0.30
seconds without inspecting term lists.

Full generated experiments using 1,024-term chunks succeeded:

| checked-in artifact | LFC3 bytes | terms | expansion chunks | header parse | slowest layer parse | final composition |
|---|---:|---:|---:|---:|---:|---:|
| SHA-256 / GF(2^128) | 28,328 | 79,093 | 104 | 1.03 s | 73.70 s | 0.24 s |
| ECDSA2 / P-256 | 49,972 | 48,256 | 54 | 17.55 s | 61.22 s | 0.24 s |

All parser-layer and expansion-chunk results are ordinary kernel theorems.
The chunks are independent and can be built in parallel; no generated module
uses `native_decide` or reads an artifact through an elaborator.

The remaining production work is selecting the formal root in the real
verifier and completing the DAG/wiring/spec certificates for the current
source-built SHA and ECDSA circuits. The two fixtures above are older
compatibility artifacts (`npublic_input = 0`); current Rust compilation reports
`npublic_input = 1`, and current SHA compilation also has 98,993 rather than
79,093 terms. They must not be silently treated as the current deployed
circuits.
