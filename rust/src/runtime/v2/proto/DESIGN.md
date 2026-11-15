# Longfellow v2 proof contract design

`runtime::v2::proto` is the contract between the v2 prover and verifier. It
defines the public proof geometry, the typed proof values, their canonical
byte encoding and parser, and the registry of transcript message tags. It
covers both fields of the v2 stack, GF(2^128) and P-256, and both complete
proof forms: the standalone `ZkProof` and the composed body that mdoc wraps
in its `MDA7` envelope. The protocols above it (witness selection, sumcheck,
the split, the adapter, dual packing, Polygero) produce and consume these
values; the transcript below it absorbs the interactive ones and seals the
whole proof. The module performs no protocol arithmetic: it only says what a
proof is, how long it is, and which bytes encode it.

## Statement

The parser starts from two things:

- the geometry, which is part of the transcript statement and reaches the
  parser only as `Bound<'_, G>` (transcript I2): the layer widths of every
  sumcheck, each field's packing degree and committed cell count `nw`, the
  Polygero dimensions `(k, s, n, t)`, and the adapter quotient width `Q`,
  a type parameter that the statement checks against `AdapterLayout` (mode
  ID `longfellow/v2/foreign/p256/two-full-field-trees/v1` for P-256);
- the proof bytes, which are untrusted.

It ends with an `Unverified<'a, P>`: a proof value `P` whose every vector has
exactly the length the geometry fixes, whose every value is canonical, and
which keeps the original bytes for the seal check (transcript I10). Parsing
grants nothing else; the protocols then verify the value, and only the seal
check yields `VerifiedProof`.

Every proof value is public. The witness is committed behind the Merkle root
in `PolygeroCommitment` and is opened only at the `t` columns the transcript
draws.

| Geometry type | Holds | Validated on construction | Absorbed in (transcript Statement) |
|---|---|---|---|
| `SumcheckProofGeometry` | `logw` of each layer, outputs to inputs | every `logw <= MAX_LOGW = 40`, and the pad count fits `usize` | `Circuit`: the circuit ID, from whose circuit the schedule derives each stage's `logw` |
| `PolygeroConfig` | `k`, `s`, `n`, `t` | by `PolygeroGeometry::new` | `JointGeometry`: Nats(k, s, n, t) |
| `PolygeroGeometry` | `nw`, `k`, `s`, `n`, `t` | `0 < t < k`, `t <= n`, `k + s <= n`, `2k <= n`, every size and `nrow * n` at most `2^28` | derived from the two above |
| `CircuitGeometry` | sumcheck geometry, packing degree `m`, `nw` | `m >= 1` (`CircuitGeometry::new`) | `Circuit`, `CommitmentLayout` |
| `ZkProofGeometry` | one `CircuitGeometry`, one `PolygeroConfig` | the Polygero geometry of `nw` under the config is valid (`ZkProofGeometry::new`) | standalone statement |
| `ComposedGeometry` | host `CircuitGeometry`, split `CircuitGeometry`, one `PolygeroConfig` | the Polygero geometry of each field's `nw` under the config is valid, and split `m = 1` (`ComposedGeometry::new`) | mdoc statement, with `AdapterLayout` for `Q` |

A proof has one Polygero profile: the spec (`ZkSpecStruct`) names one, and
its `(k, s, n, t)` is the single `PolygeroConfig` of the proof geometry
(I8). Every committing field uses it.

`nrow = ceil(nw / (k - t)) + 3`: the data rows of `nw` witness cells, plus
the Polygero rows `u`, `m` and `f*`. Merkle leaf and node hashes use the
fixed domain `DOMAIN` (`runtime/v2/merkle/hash.rs`) (transcript I3), so no digest of the
geometry exists: the statement alone binds it, and nothing derived from it
is on the wire.

## Invariants

Code comments cite these as "proto I1" and so on.

**I1. One magic, outermost; the proof is prover data.** A complete proof is
`magic || body || seal`. The magic is four ASCII bytes naming the byte format
(`MDA7`, `LFV9`); the seal is the 32-byte first PRF block of the seal node.
The body contains only values the prover computed: no nested magic, no
context copy, no geometry value. Its only integer is the frontier count
(transcript I11).
*Enforced by:* the body writers have no constant to write and the geometry
types have no wire form (type); a test that the proof length equals
`4 + B(g) + 8 + 32 f + 32` (I3).

**I2. The bound geometry drives parsing.** Every public reader takes its
geometry as `&Bound<'_, G>`, so the verifier parses the proof against exactly
the geometry the statement absorbed. The public readers are the complete
ones, `ZkProof::read` and `MdocProof::read`. Every component reader
(sumcheck, circuit, fingerprint, composed body, Polygero bodies, Merkle,
adapter message) is crate-private, is compiled only in role builds and
tests, and is called only by the complete readers, which pass it
sub-geometries read through `g.part()`. The adapter message reader is the
supertrait `proto::composed::sealed::Read` of `AdapterMessage`, in a
crate-private module, so outside the crate it cannot be implemented. Generic
code outside the crate still sees the inherited method through an
`AdapterMessage` bound, so the reader also takes a `sealed::Token`, which
only `proto::composed` constructs: outside the crate it cannot be called.
`Bound::project` is never needed for parsing.
*Enforced by:* no public read function takes a plain geometry (type);
visibility of the component readers, the sealed adapter reader and its
token (type; compile_fail doctests, including a call through an
`AdapterMessage` bound); a test that the absorbed geometry equals the
parsing geometry (transcript I3).

**I3. Lengths come from the geometry, checked before decoding.** Every field's
length is a function of the geometry, except the Merkle frontier. The body
states the frontier's digest count `f` in one u64 word just before the
frontier, the last body field. The parser computes the fixed length `B(g)`
of every field before that word, reads `f` at offset `4 + B(g)`, and
requires `|bytes| = 4 + B(g) + 8 + 32 f + 32` with
`0 <= f <= t (ceil(log2 n) + 1) <= 2^32 - 1` (`MAX_FRONTIER`, the formal
model's cap, which every valid geometry stays below), in checked
arithmetic. Nothing is decoded or allocated before this check, so
allocation is bounded by the input length, and no read can run past the
input.
*Enforced by:* the single length check (`checked_body`) at the top of each
complete reader (runtime); validated geometry, and `B(g)` computed with
checked arithmetic (I8); a per-reader test that every truncation and every
extension fails.

**I4. Wire order is send order.** The body is the interactive section, each
field in the order the schedule sends it, then the terminal section. Each
proof field is exactly one of: interactive (it has a tag and is absorbed when
sent) or terminal (Polygero rows, Merkle nonces, the frontier count and the
frontier: covered only by the seal) (transcript I4). The magic is covered
only by the seal.
*Enforced by:* the classification table below and the field order of each
proof struct; the role-trace test, which checks that the absorbed messages,
in order, cover the interactive section byte for byte (I5).

**I5. Wire payload equals absorbed payload.** The wire form of an
interactive field is the concatenation of its message's value payloads, in
the message's value order, without the transcript headers (tag, kind, field
ID, count): Elements give their canonical serializations, Bytes their
bytes, Bits their packed bytes (transcript I5). Lengths are omitted because
the geometry and the tag schema fix them.
*Enforced by:* the role-trace test strips the headers from the absorbed
messages and compares the result with the interactive section of the proof.

**I6. One encoding per proof value.** The parser accepts exactly the bytes
the writer produces. A field element must equal the field's own encoding of
the decoded value (`read_field` re-encodes and compares), which rejects
aliases and P-256 values at or above the modulus. A `MaskedWord<Q>` must have
zero padding bits. The frontier must have exactly the digests the drawn
columns need, no more and no fewer. Nothing may follow the frontier in the
body, and nothing may follow the seal.
*Enforced by:* `read_field` and `MaskedWord::read` (runtime); the body
readers reject bytes after the frontier, and `verify_proof` consumes the
frontier exactly (runtime); the alias tests in `proto/tests.rs`; Lean
`ProofOutput.read_canonical`.

**I7. One tag registry.** Every transcript tag is a variant of the
`#[repr(u64)]` enum `Tag` in `proto/tags.rs`, with its schema in
`Tag::schema` (transcript I6). Tags 0 to 15 are the transcript's
terminators and are not variants. The file depends on nothing, so the
transcript can name `Tag` without depending on the rest of this module.
*Enforced by:* the compiler (E0081 on a repeated discriminant; a `Message`
impl must name a variant; `Tag::schema` is an exhaustive match); the
dependency rule `runtime/v2/proto/tags:` with no dependencies; the trace
checks of transcript I6.

**I8. Geometry is valid and stated once.** Geometry types have private fields
and validating constructors, so every geometry value that reaches a reader or
writer is valid. The Polygero dimensions exist once per proof geometry
(`PolygeroConfig`), and each field's `PolygeroGeometry` is derived from it
and that field's `nw`, so two fields cannot disagree on `k, s, n, t`.
*Enforced by:* private fields and `Result`-returning constructors (type);
`ComposedGeometry` and `ZkProofGeometry` hold one config, and derive each
field's `PolygeroGeometry` in `polygero()` (type); the test
`proof_geometries_are_checked_and_derive_their_polygero_geometry`.

**I9. The contract uses only shared code.** Files under `runtime/v2/proto`
use only `core`, `util`, `runtime::algebra` and the transcript framing
(`runtime::v2::transcript`), never a protocol implementation or a role
(AGENTS.md).
*Enforced by:* `proto_allows` in `bin/dependency_check/main.rs` and the
`runtime/v2/proto*` lines of `rules.txt`; the `prover_only` and
`verifier_only` builds.

## Proof layout

### Composed body (mdoc)

Fields in wire order, which is send order (I4). `w_H = 16` (GF(2^128)),
`w_S = 32` (P-256). `L_H`, `L_S` are the host and split layer lists, `m` the
host packing degree, `nrow_H`, `nrow_S` the row counts. The challenges drawn
between fields are those of the transcript challenge schedule; they are not
on the wire.

| # | Field | Rust (`ComposedProof`) | Class | Tag | Bytes |
|---|---|---|---|---|---|
| 1 | Merkle root | `commitment` | interactive | `Commitment` 32 | 32 |
| 2 | host fingerprint responses | `fingerprints.0` | interactive | `FingerprintResponse` 33 | `2 w_H` |
| 3 | split fingerprint responses | `fingerprints.1.0` | interactive | `FingerprintResponse` 33 | `2 w_S` |
| 4 | split sumcheck, per layer: `logw` rounds, cross, claims | `split` | interactive | `SumcheckRound` 48, `SumcheckCross` 49, `SumcheckClaims` 50 | `w_S sum_{L_S} (2 logw + 3)` |
| 5 | split opening `mu` | `mu` | interactive | `SplitOpening` 64 | `w_S` |
| 6 | masked quotients (the adapter message) | `message` | interactive | `P256AdapterQuotients` 65 | `2 ceil(Q/8)` |
| 7 | host sumcheck, per layer as in 4 | `host.sumcheck_proof` | interactive | 48, 49, 50 | `w_H sum_{L_H} (2 logw + 3)` |
| 8 | packing `U` (only if `m > 1`) | `host.packing` | interactive | `PackingU` 80 | `m w_H` |
| 9 | packing `A` (only if `m > 1`) | `host.packing` | interactive | `PackingA` 81 | `w_H` |
| 10 | host `H`, then `Z` | `polygero` body 0 | interactive | `PolygeroResponse` 96 | `(3k + s) w_H` |
| 11 | split `H`, then `Z` | `polygero` body 1 | interactive | `PolygeroResponse` 96 | `(3k + s) w_S` |
| 12 | host opened rows | `polygero` body 0 | terminal | none | `t nrow_H w_H` |
| 13 | split opened rows | `polygero` body 1 | terminal | none | `t nrow_S w_S` |
| 14 | Merkle nonces | `polygero` opening | terminal | none | `32 t` |
| 15 | Merkle frontier count `f` | `polygero` opening | terminal | none | 8 |
| 16 | Merkle frontier | `polygero` opening | terminal | none | `32 f` |

The split participant has packing degree one by construction (split storage
requires a degree-one prime frontend), so its proof is a bare
`SumcheckProof` and has no packing field. `B(g)` is the sum of rows 1 to 14.
For the rate-1/7 profile `(k, s, n, t) = (349, 12, 2443, 84)` with `m = 128`
and `Q = 10`: rows 10 and 11 are 16,944 and 33,888 bytes, row 14 is 2,688
bytes, rows 8 and 9 are 2,064 bytes, row 6 is 4 bytes, and `f <= 84 * 13 =
1,092`.

### Pure-foreign split

A pure-foreign split participant stores every value as bits in the binary
commitment and commits no cells of its own. Its statement part is a
`CommitmentLayout` with zero committed private cells, zero pad cells and zero
fingerprint mask cells, and it is not a joint field: it has no Polygero
geometry, no fingerprint masks and no rows. It needs no mask `R`, so there is
no split opening; its row weights are a `Challenge` input drawn at the
frontend's last boundary (transcript I8).

`ComposedProof` is the body of the mixed composition only: it always holds
two fingerprint responses, `mu` and two field bodies. A composition with a
pure-foreign split is future work. Its body would be the table above without
rows 3, 5, 11 and 13, with every remaining field keeping its class and
position. Lean models the row batching (`RowBatching`, `PureHandoff`,
`PureComposition`), but no application may use pure-foreign storage until
its application model charges those events.

### Standalone body (`ZkProof`)

| # | Field | Class | Tag | Bytes |
|---|---|---|---|---|
| 1 | Merkle root | interactive | `Commitment` | 32 |
| 2 | fingerprint responses | interactive | `FingerprintResponse` | `2 w` |
| 3 | sumcheck | interactive | 48, 49, 50 | `w sum (2 logw + 3)` |
| 4 | packing `U`, `A` (only if `m > 1`) | interactive | `PackingU`, `PackingA` | `(m + 1) w` |
| 5 | `H`, then `Z` | interactive | `PolygeroResponse` | `(3k + s) w` |
| 6 | opened rows | terminal | none | `t nrow w` |
| 7 | Merkle nonces | terminal | none | `32 t` |
| 8 | Merkle frontier count `f` | terminal | none | 8 |
| 9 | Merkle frontier | terminal | none | `32 f` |

### What the parser checks

In this order, all before any protocol runs. `ZkProof::read` reports a
failure as an `std::io::Error` (`InvalidData` or `UnexpectedEof`),
`MdocProof::read` as an error string.

| Check | Where |
|---|---|
| `|bytes| = 4 + B(g) + 8 + 32 f + 32`, with `f` the u64 at offset `4 + B(g)` and `0 <= f <= t (ceil(log2 n) + 1)` | complete reader, first (`checked_body`, I3) |
| magic equals the envelope's constant | complete reader |
| each field element canonical | `read_field` (I6) |
| each `MaskedWord<Q>` has zero padding bits | `MaskedWord::read` (I6) |
| the frontier has exactly `f` digests and ends the body | `MerkleProof::read_path`, `JointPolygeroProof::read` |
| exactly the seal block remains | `Unverified::decoded` |

Verification adds two byte-level checks: the frontier holds exactly
`frontier_len(n, I)` digests for the drawn column set `I` (`verify_proof`),
and the seal equals the transcript's seal block.

## Formats

All integers are u64 little endian. The body's only integer is the frontier
count.

```text
mdoc_proof := "MDA7" composed seal
zk_proof   := "LFV9" zk_body seal
seal       := byte{32}                      ; first PRF block of the seal node

composed   := root fp(H) fp(S) sumcheck(S) mu quotients
              sumcheck(H) packing(H)
              response(H) response(S)       ; end of the interactive section
              rows(H) rows(S) nonce{t} frontier
zk_body    := root fp(F) sumcheck(F) packing(F) response(F)
              rows(F) nonce{t} frontier

root       := byte{32}
fp(F)      := elem(F){2}
sumcheck(F):= layer(F, logw){for each layer, outputs to inputs}
layer(F,l) := (elem(F) elem(F)){l} elem(F) elem(F) elem(F)  ; rounds (c0-s0, c1-s1), cross, claims
mu         := elem(P256)
quotients  := word(Q) word(Q)               ; one per conversion tree
word(Q)    := byte{ceil(Q/8)}               ; GF(2)^Q, bit j at byte j/8 bit j%8, padding zero
packing(F) := ""                            ; m = 1
            | elem(F){m} elem(F)            ; U, then A
response(F):= elem(F){k+s} elem(F){2k}      ; H, then Z: oracle-prefix evaluations
rows(F)    := (elem(F){t}){nrow}            ; rows u, m, witness 0..nrow-3, f*; t values each, in query order
nonce      := byte{32}                      ; salt of the q-th drawn column, in query order
frontier   := u64(f) byte{32}{f}            ; the last body field
elem(F)    := canonical serialization of F (GF(2^128): 16 bytes; P-256: 32 bytes)
```

The frontier lists, for heap nodes `i = n-1` down to `1` that lie on a path
from a drawn leaf, the sibling of the one child on the path, when exactly one
child is on it. Its length `f = frontier_len(n, I)` is a function of `n` and
the drawn columns, which the verifier knows only after replaying the
transcript; this is why the frontier is last and why the body states its
count.

### Commitment preimages

Polygero owns these; they appear here because the Merkle types are part of
the contract. Domain strings are raw bytes without a length.

```text
leaf(j)    := SHA-256("polygero/joint/leaf/v1" || DOMAIN || u64(j) || salt_j
                      || for each field in participant order:
                         elem(row_r[j]) for r in 0..nrow)
node(i)    := SHA-256("polygero/joint/node/v1" || DOMAIN || u64(i) || left || right)
                                            ; heap index i >= 1, leaves at n..2n
DOMAIN     := "longfellow/v2/merkle/domain" || 0x00{5}   ; 32 bytes, `DOMAIN` (runtime/v2/merkle/hash.rs)
```

### Magics

| Magic | Proof | Writer and reader |
|---|---|---|
| `MDA7` | mdoc composed proof | `MdocProof` in `mdoc/runtime/v2/proto.rs` |
| `LFV9` | standalone `ZkProof` | `ZkProof` in `runtime/v2/proto/zk.rs` |

The seal message (`Seal`, tag 112) carries every proof byte before the seal
block, the magic included.

These are the only complete proofs. Sealed bare Polygero bodies
(`JointPolygeroParam::write` and `read`) exist only for tests and tools
(`test`, `testonly` and `tooling` builds), so I1 does not apply to them.

### Tag registry

`runtime::v2::proto::tags::Tag`, in `runtime/v2/proto/tags.rs`. Ranges group
tags by owning component. `F` is the sending component's field. The message
view types that implement `Message` live with the component that sends them,
next to its schedule; the values they borrow are the proof types of this
module.

| Range | Tag | Variant | Schema | Message owner | Proof value |
|---|---|---|---|---|---|
| 0..15 | | terminators | | transcript | |
| 16..31 | 16 | `MdocStatement` | see transcript Statement | mdoc statement | |
| | 17 | `ZkStatement` | Bytes, Bytes | standalone statement | |
| | 18 | `Circuit` | Bytes(32) | statement | |
| | 19 | `CommitmentLayout` | Nats(4), Bytes, Nats, Nats, Nats(2) | statement | |
| | 20 | `JointGeometry` | Nats(4) | statement | |
| | 21 | `PublicInputs` | Elements(F, n) | statement | |
| | 22 | `AdapterLayout` | Bytes, Nats(3), Nats | statement, one per adapter | |
| 32..47 | 32 | `Commitment` | Bytes(32) | `polygero` | `PolygeroCommitment` |
| | 33 | `FingerprintResponse` | Elements(F, 2) | `witness_selection` | `FingerprintResponse<E>` |
| 48..63 | 48 | `SumcheckRound` | Elements(F, 2) | `sumcheck` | `RoundPoly` |
| | 49 | `SumcheckCross` | Elements(F, 1) | `sumcheck` | `LayerProof::cross` |
| | 50 | `SumcheckClaims` | Elements(F, 2) | `sumcheck` | `LayerProof::claims` |
| 64..79 | 64 | `SplitOpening` | Elements(P256, 1) | `zk::split` | `ComposedProof::mu` |
| | 65 | `P256AdapterQuotients` | Bits(Q), Bits(Q) | `foreign::adapter` (P-256 mode) | `ComposedProof::message`, a `[MaskedWord<Q>; 2]` |
| 80..95 | 80 | `PackingU` | Elements(F, m) | `dual_packing` | `PackingProof::TraceZero::u` |
| | 81 | `PackingA` | Elements(F, 1) | `dual_packing` | `PackingProof::TraceZero::a` |
| 96..111 | 96 | `PolygeroResponse` | Elements(F, k+s), Elements(F, 2k) | `polygero` | `FieldProof::h`, `FieldProof::z` |
| 112.. | 112 | `Seal` | Bytes | transcript seal | all bytes before the seal block |

A schema change, or a second message shape for the same step, takes a new
tag; another adapter mode gets its own quotient tag next to
`P256AdapterQuotients`. There are no round labels: boundaries are implied by
the schedule (transcript I7).

## Rust API

```rust
// runtime::v2::proto::tags: proto/tags.rs, dependency component with no dependencies (I7)
#[repr(u64)]
pub enum Tag {
    MdocStatement = 16, ZkStatement = 17, Circuit = 18, CommitmentLayout = 19,
    JointGeometry = 20, PublicInputs = 21, AdapterLayout = 22,
    Commitment = 32, FingerprintResponse = 33,
    SumcheckRound = 48, SumcheckCross = 49, SumcheckClaims = 50,
    SplitOpening = 64, P256AdapterQuotients = 65,
    PackingU = 80, PackingA = 81,
    PolygeroResponse = 96,
    Seal = 112,
}
impl Tag {
    pub const ALL: [Tag; 18];
    pub const fn schema(self) -> &'static [Value];   // exhaustive match
    pub fn admits(self, values: &[(u64, u64)]) -> bool;
}

// geometry: private fields, validating constructors, accessors (I8)
pub const MAX_LOGW: usize = 40;
pub struct SumcheckProofGeometry { logw_layers: Vec<usize> }
impl SumcheckProofGeometry {
    pub fn new(logw_layers: Vec<usize>) -> std::io::Result<Self>;
    pub fn layers(&self) -> &[usize];
    pub fn serialized_elements(&self) -> usize;      // sum (2 logw + 3)
    pub fn pad_count(&self) -> usize;                // sum (2 logw + 4)
}
pub struct PolygeroConfig { pub k: usize, pub s: usize, pub n: usize, pub t: usize }
pub struct PolygeroGeometry { /* nw, k, s, n, t: crate-private */ }
impl PolygeroGeometry {
    pub fn new(nw: usize, config: PolygeroConfig) -> std::io::Result<Self>;
    pub fn config(&self) -> PolygeroConfig;
    pub fn nrow(&self) -> usize;                     // ceil(nw / (k - t)) + 3
    pub fn response_lengths(&self) -> [usize; 2];    // [k + s, 2k]
}
pub struct CircuitGeometry { sumcheck: SumcheckProofGeometry, packing_degree: usize, nw: usize }
impl CircuitGeometry {
    pub fn new(sumcheck: SumcheckProofGeometry, packing_degree: usize, nw: usize)
        -> std::io::Result<Self>;                    // packing degree >= 1
    pub fn sumcheck(&self) -> &SumcheckProofGeometry;
    pub fn packing_degree(&self) -> usize;
    pub fn nw(&self) -> usize;
}
pub struct ZkProofGeometry { circuit: CircuitGeometry, config: PolygeroConfig }
impl ZkProofGeometry {
    pub fn new(circuit: CircuitGeometry, config: PolygeroConfig)
        -> std::io::Result<Self>;                    // the Polygero geometry is valid
    pub fn circuit(&self) -> &CircuitGeometry;
    pub fn config(&self) -> PolygeroConfig;
    pub fn polygero(&self) -> PolygeroGeometry;      // derived, never stored
}
pub struct ComposedGeometry { host: CircuitGeometry, split: CircuitGeometry, config: PolygeroConfig }
impl ComposedGeometry {
    pub fn new(host: CircuitGeometry, split: CircuitGeometry, config: PolygeroConfig)
        -> std::io::Result<Self>;                    // split packing degree 1; both Polygero geometries valid
    pub fn host(&self) -> &CircuitGeometry;
    pub fn split(&self) -> &CircuitGeometry;
    pub fn config(&self) -> PolygeroConfig;
    pub fn polygero(&self) -> [PolygeroGeometry; 2]; // host, split: derived, never stored
}

// proof values
pub struct Digest { pub data: [u8; 32] }
pub const NONCE_LEN: usize = 32;
pub struct PolygeroCommitment { root: Digest }
pub const FINGERPRINTS: usize = 2;
pub struct FingerprintResponse<E> { pub values: [E; FINGERPRINTS] }
pub struct RoundPoly<const W: usize, F> { pub coefficients: [F::E; 2] }
pub struct LayerProof<const W: usize, F> { pub rounds: Vec<RoundPoly<W, F>>, pub cross: F::E, pub claims: [F::E; 2] }
pub struct SumcheckProof<const W: usize, F> { pub layers: Vec<LayerProof<W, F>> }
pub enum PackingProof<E> { Direct, TraceZero { u: Vec<E>, a: E } }
pub struct CircuitProof<const W: usize, F> { pub sumcheck_proof: SumcheckProof<W, F>, pub packing: PackingProof<F::E> }
pub struct FieldProof<E> { h: Vec<E>, z: Vec<E>, rows: Vec<E> }  // h, z interactive; rows terminal
pub struct JointPolygeroProof<B> { bodies: B, opening: MerkleProof } // B: (FieldProof<E>, tail)
pub(in crate::runtime::v2) struct MerkleProof { nonce: Vec<MerkleNonce>, path: Vec<Digest> }

// the adapter's message (foreign::word implements it for [MaskedWord<Q>; 2])
pub trait AdapterMessage: sealed::Read {
    const BYTES: usize;
    fn write(&self, out: &mut Vec<u8>);
}
pub(crate) mod sealed {
    pub struct Token(/* constructed only in proto::composed */);  // role builds
    pub trait Read: Sized {                          // read: role builds only
        fn read(b: &mut &[u8], token: Token) -> Result<Self, String>;
    }
}

// standalone complete proof
pub struct ZkProof<const W: usize, F> {
    pub com: PolygeroCommitment,
    pub fingerprints: FingerprintResponse<F::E>,
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub packing: PackingProof<F::E>,
    pub com_proof: JointPolygeroProof<(FieldProof<F::E>, ())>,
}
impl<const W: usize, F> ZkProof<W, F> {
    pub const MAGIC: [u8; 4] = *b"LFV9";
    pub fn write(&self, g: &ZkProofGeometry, f: &F, transcript: Transcript)
        -> std::io::Result<EncodedProof>;
    pub fn read<'a>(bytes: &'a [u8], g: &Bound<'_, ZkProofGeometry>, f: &F)
        -> std::io::Result<Unverified<'a, Self>>;
}

// composed body; applications add the magic and the seal
pub struct ComposedProof<const WH: usize, H, const WS: usize, S, M> {
    pub commitment: PolygeroCommitment,
    pub fingerprints: (FingerprintResponse<H::E>, (FingerprintResponse<S::E>, ())),
    pub split: SumcheckProof<WS, S>,
    pub mu: S::E,
    pub message: M,                                  // M: AdapterMessage
    pub host: CircuitProof<WH, H>,
    pub polygero: JointPolygeroProof<(FieldProof<H::E>, (FieldProof<S::E>, ()))>,
}
impl<..> ComposedProof<WH, H, WS, S, M> {
    pub fn fixed_len(g: &ComposedGeometry, h: &H, s: &S) -> Option<usize>; // B(g)
    pub fn write_to_buf(&self, out: &mut Vec<u8>, g: &ComposedGeometry, h: &H, s: &S)
        -> Result<(), String>;
    pub(crate) fn read(body: &[u8], g: &ComposedGeometry, h: &H, s: &S)
        -> Result<Self, String>;                     // exactly the whole body
}

// mdoc::runtime::v2 envelope
pub struct MdocProof<F1, F2> { pub body: ComposedProof<2, F1, 4, F2, [MaskedQuotient; 2]> }
impl MdocProof<F1, F2> {
    pub const MAGIC: [u8; 4] = *b"MDA7";
    pub fn write(&self, g: &ComposedGeometry, f1: &F1, f2: &F2, transcript: Transcript)
        -> Result<EncodedProof, String>;
    pub fn read<'a>(bytes: &'a [u8], g: &Bound<'_, ComposedGeometry>, f1: &F1, f2: &F2)
        -> Result<Unverified<'a, Self>, String>;
}
```

How the API enforces the invariants:

- Writers take the `Transcript` by value and end in its crate-private
  `append_final_seal`, so a proof is written once and is always sealed (I1,
  transcript I10). The prover hands the writer the geometry it opened its
  statement with.
- Public readers take `&Bound<'_, G>` and hand sub-geometries from
  `g.part()` to the component readers (`SumcheckProof`, `CircuitProof`,
  `FingerprintResponse`, `ComposedProof`, `FieldProof`, `MerkleProof`, the
  adapter message), which are crate-private (I2).
- The complete reader checks the total length before it reads any field, so
  component readers cannot see a short input (I3).
- `ComposedProof` lists its fields in send order and `FieldProof` splits the
  interactive response from the terminal rows, so the writer's field order is
  the wire order (I4).
- `MaskedWord<N>` (in `foreign::word`) holds a value below `2^N` by
  construction: its reader rejects padding bits, and its only constructor
  masks a `Word<N>` with an `Otp<N>` (I6). The contract names only the
  `AdapterMessage` trait, so it names no protocol type (I9).
- No geometry type but `PolygeroConfig` has public fields, and none has a
  wire form (I1, I8).

The proto types are values only. Each sending component wraps them in a
borrowed `Message` view (for example a `PolygeroResponse` view with its field)
and sends it through its `TranscriptRef`; the verifier sends the parsed values
through the same views (transcript I9).

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Parsing against a geometry other than the absorbed one | I2: public readers take `Bound` |
| Parsing one component against an arbitrary geometry | I2: component readers are crate-private, and the adapter message reader is sealed and needs a crate-private token |
| A truncated or extended proof read partway, or a huge allocation from a hostile count | I3: one total-length check first; the one count on the wire, the frontier count, is capped by the geometry |
| Wire order differing from absorb order | I4: struct order is send order; role-trace test |
| A field absorbed but not on the wire, or on the wire but not absorbed nor terminal | I4: classification table; role-trace test |
| Wire bytes and absorbed bytes of one message disagreeing | I5: role-trace payload comparison |
| Two encodings of one proof (aliased element, nonzero padding, extra frontier digest, trailing bytes) | I6: canonical readers, exact frontier, length check |
| A nested magic or a context copy disagreeing with the geometry | I1: neither is on the wire |
| Host and split disagreeing on `k, s, n, t` | I8: one `PolygeroConfig` per proof geometry |
| An invalid geometry reaching a reader, or an overflowing `B(g)` | I8: validating constructors, `MAX_SIZE`, `MAX_LOGW` |
| A split frontend with a packing response | `ComposedProof::split` is a `SumcheckProof`; `ComposedGeometry::new` requires degree 1 |
| Two messages with one tag, or a tag colliding with a terminator | I7: E0081; variants start at 16 |
| Another adapter mode reusing tag 65 | I7: tag 65 is `P256AdapterQuotients`; each mode has its own tag |
| The contract depending on a protocol or a role | I9: `proto_allows`, role builds |
| A writer emitting a value of the wrong shape | every writer validates against the geometry and returns an error |

## Soundness and zero knowledge

The contract contributes no error term of its own. Its checks make the
protocols' bounds apply to the bytes the verifier actually reads.

| Check | Purpose | Lean |
|---|---|---|
| Canonical parsing (I6), length check (I3) | The encoding is injective and the parser is its left inverse, so the view and every oracle query are functions of the proof value; no proof has a second accepted encoding | `ProofBodyReplay.body_bytes_injective`; `ProofOutput.read_canonical` (a successful parse accounts for every byte, the seal included) |
| Geometry from `Bound` (I2) | The verifier checks the proof of the absorbed instance, which the soundness statement quantifies over | transcript header codec (transcript I1, I3) |
| Interactive fields absorbed in send order (I4, I5) | Each challenge depends on every message before it; the component bounds then apply, and the boundary count enters only as `r/2^256` | `ProofBodyCodec` (body grammar), the transcript message codec |
| Seal over all bytes (I1) | Binds the terminal fields and the magic. An accepted seal at an unqueried final point contributes the `2^-256` guessing term; otherwise the seal forces the final oracle query. The seal is query accounting: it does not make an invalid body valid, which the other checks rule out | `TranscriptV2.final_seal_guess_ratio_le` (unqueried point); `TranscriptV2.Chain.required_fresh_queries` (forced queries); the seal's two queries count in `Q` |
| Exact frontier, position-bound nodes | One opening per column set; leaf and node preimages are injective and domain separated | `MerkleWireCodec.codec_inj`, `domains_ne` |
| Geometry caps | The proof space is finite, which the extractor's finite search needs | `OpeningBody.frontierCapacity`, the `Fintype` instance of `OpeningBody.Authentication` |
| Two-byte quotient words with zero padding | The advice parser is canonical | `MdocAdvice.codec`, `word_length` |

Zero knowledge. Every interactive value is masked by its component: sumcheck
pads, packing masks, fingerprint masks, `mu` by the uniform `R`, the
quotients by their one-time pads. The terminal rows reveal only the `t`
opened columns of masked rows. Each column has an independent 32-byte salt,
which gives indexed-leaf hiding; the whole complete view is within
`(Qpre+Qpost)/2^256` of the simulator (`Mdoc.ZeroKnowledge.statClose`, with
the commitment hop in `StrandCanonicalCommitmentHiding`). The proof length
reveals `f`, which is a function of the public column indices only.

## Open questions

1. **Wire payload by construction.** I5 rests on a test because the wire
   writer and the `Message` views are separate code. Recommendation: let the
   transcript's encoder write to a payload-only sink as well, so the
   interactive section is produced by the same `encode` that absorbs it.
