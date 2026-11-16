# Longfellow v2 transcript design

The v2 transcript is a Fiat–Shamir transcript over numbered SHA-256 strands.
It opens with one statement that fixes the whole instance. After the
statement it absorbs only prover messages, each exactly once, in one
encoding. A strand node ends exactly where a challenge follows a message, and
every sub-protocol starts with a prover message. Each rule below names what
enforces it: the type system, a runtime check, a test, or Lean.

## Invariants

Code comments and other design documents cite these as "transcript I1" and so
on.

**I1. The statement comes first and only once.** The transcript opens with the
statement: protocol ID, context, the complete spec, every circuit ID, the
complete proof geometry, and every circuit public input of every field. No
other code absorbs setup or public data.
*Enforced by:* outside the crate a session opens only through
`Opened::new(statement)`, since `Transcript::new` is crate-private (type);
`Transcript::new` writes the statement's `Identity` message first, then the
rest of the statement; the Lean header codec.

**I2. Components read bound values from the transcript.** A component gets its
circuit, geometry, parameters and public inputs only through
`Bound<'_, Part>`, which borrows the part and the transcript together.
Outside the crate a `Bound` comes only from a named accessor of an `Opened`
session, which binds a part of the statement the session opened with:
`Opened::geometry` for `ZkProofStatement` and `ComposedStatement`. Binding
an arbitrary value (`Transcript::bound`, `Opened::bound`, `Bound::project`
and the joint drivers' `bound`) is crate-private. The proof reader takes its
geometry the same way, so the verifier parses and checks the proof against
exactly the geometry it absorbed. A component cannot use a value that was
not absorbed, or a value absorbed into a different transcript.
The `Statement`, `Message` and `SetupMessage` traits are open: an
implementation outside the crate is trusted to write its values faithfully,
and it gets no `Bound`, since only the crate's statement types have
accessors. Under the `testonly` feature,
`Transcript::bound_for_test` binds any value to a bare session, for benches
and tools.
A state that spans several calls (witness selection, joint Polygero) records
the session's stamp when it is created and checks it on every later call, so
it cannot be completed on another transcript.
*Enforced by:* no public prove, verify or read function takes a
public-input, circuit or geometry parameter, and binding is crate-private
(type; compile_fail doctests); the session stamp check (runtime).

**I3. The statement fixes the instance: circuits and geometry, once.** Every
circuit ID is absorbed, including the adapter fragment, next to the combined
hash. The ID hashes the whole circuit, its field and shape included (output,
input and public input counts, each layer's width), so the statement binds
the shape through the ID. So is the complete proof geometry: each field's
commitment layout (packing descriptor, cell counts, storage runs, mask,
fingerprint cells) and the joint Polygero profile. They are written once, in
the statement, as values rather than digests. After the statement only
prover messages are absorbed. Digests computed from these values (statement
digests) are not absorbed, since their inputs already are. Merkle leaf and
node hashes use the fixed domain `DOMAIN` (`runtime/v2/merkle/hash.rs`), so the statement is
the only place the parameters are bound. The verifier fixes the evaluation
domain, and no message binds it.
*Enforced by:* Rust. Setup messages implement `SetupMessage`, which only a
statement's `Header` writes (type). The geometry messages are written from
the participants themselves; the parsing geometry (`ZkProofGeometry`,
`ComposedGeometry`) is a copy derived from the same participants, so it
agrees with them by construction. Tests check that the absorbed geometry
equals the parsing geometry (the mdoc trace test, for the profile against
the parsing geometry's and the spec's), that the statement precedes every
prover message, that every message has its tag's schema, and the golden
pins of the standalone transcript and the mdoc first node. Lean does not prove I3: its model takes the statement messages
after the combined hash as fixed setup bytes.

**I4. Every prover message is absorbed exactly once, when sent.** Each
proof-body field is either interactive (it has a tag and is absorbed where it
is sent) or terminal (sent after the last challenge: Polygero rows, Merkle
nonces, the frontier count and the frontier, covered only by the seal). The
`Seal` message is the one deliberate exception: its Bytes value is the whole
proof before the seal block, so it covers the interactive fields a second
time together with the terminal fields and the magic. It binds the complete
proof, not any single message, and it is the last message of every proof.
*Enforced by:* a test that the send trace covers each interactive field once;
the Lean message codec.

**I5. One encoding.** A message is a tag followed by its values. Every value
is a vector with its length, of one of four kinds: Bytes, Nats (u64
integers), Elements (elements of a registered field, with its field ID) or
Bits. A registered field (`RegisteredField`) is one whose `FieldID` names it
alone and whose canonical serialization has one width: P-256 and GF(2^128).
A single integer or field element is a vector of length one; there is no
scalar kind. Every integer is u64 little endian.
*Enforced by:* the encoder has no scalar or raw-bytes method, and
`Encoder::elements` takes only a `RegisteredField` (type); Lean proves the
grammar injective (`Grammar.nodes_injective`) and that the deployed codecs
encode as the grammar (`TaggedGrammar`), whose kernel-checked test parses the
Rust golden node payloads with the deployed tag registry.

**I6. Unique tags with fixed schemas.** All tags live in one `#[repr(u64)]`
registry, `runtime::v2::proto::tags`, a module with no dependencies so that
the transcript can name `Tag`; a repeated value is compile error E0081.
Each tag has one fixed list of values, its schema (`Tag::schema`), so the
tag alone determines how to parse the message. The encoder's kind codes, the
trace checks and the test decoder all read that one table.
*Enforced by:* the compiler (unique discriminants, and `Tag::schema` is an
exhaustive match); trace checks that hold every message of a complete proof
to its tag's schema (`Tag::admits`), and cover every tag.

**I7. A boundary is a message followed by a challenge.** A strand node ends
exactly when a challenge is drawn after at least one message. Draws with no
message in between read further from the same stream, whichever step makes
them: a sub-protocol's leading draw reads the stream of the boundary that
the previous step's last message closed, after whatever that step itself
drew from it. No node lacks a message, and rounds carry no labels.
*Enforced by:* the transcript state machine, which has no other way to end a
node; the Lean round schedule.

**I8. Each sub-protocol draws its own challenges.** Every sub-protocol that
draws a challenge (sumcheck, the split, the adapter, witness selection, dual
packing, Polygero) either begins by sending, or draws its leading challenge
on entry, before its first message, from the boundary the preceding message
closed (I7): the sumcheck top weights, eta and the adapter's conversion pair.
A sumcheck whose circuits all have zero layers sends nothing; its top
weights are its input assertions. No challenge crosses a call: each step
draws its challenges and uses them in the same call, so no caller holds one
between the draw and the use, hands one to two consumers, or sends a message
in between. What a challenge depends on is fixed by the messages already
absorbed and by the arguments of the call that draws it, which exist before
the draw: the host frontend's virtual-input definitions are an argument of
the call that draws its top weights, and the split's foreign claim of the
adapter call that draws the conversion pair. Likewise the Polygero batching
weights are drawn by the joint opening (`JointProver::finish`,
`JointVerifier::finish`, through Polygero's `prove` and `reduce`), which
takes each field's equations, typed per field, and the row weights of
pure-foreign storage by the pure split step (`PureClaim::batch`), which
takes the frontend's claim; so the weights batch exactly the system the call
was given, and no other can be substituted. Each `LinearStatement` also
carries the stamp of the session that derived it, and the joint opening
rejects equations from another session.
*Enforced by:* the leading draws are inside the sumcheck, split and adapter
entry points, and no entry point takes a challenge as a parameter (type);
the batching weights are drawn inside the call that takes the statements,
and no item returns or accepts them (type); the equations' session stamp
check (runtime); the drivers' fixed order of calls, checked by the
role-trace test (I9) and the golden vectors.

**I9. Prover and verifier run one schedule.** The send and draw sequence
lives in shared code called by both roles. A test records the trace of tags
and draw kinds in each role (bytes, elements, nonzero elements and indices,
each its own kind, with the index values) and asserts that they are equal,
and the boundary count is checked against Lean.
*Enforced by:* the role-trace test; `check_mdoc_round_shapes`.

**I10. Every proof ends in the seal.** The last node holds the Seal message
with the whole proof body and ends with the seal terminator. Its first PRF
block is appended to the proof, and complete verification requires it.
*Enforced by:* `VerifiedProof` is obtained only from the seal check, which
takes the `Unverified` proof and the session by value. Outside the
transcript the check is reached only through `zk::Authenticated::check_seal`.
An `Authenticated` exists only after the joint opening check of the
`Unverified` proof it keeps (zk I7), so no seal is checked on an
unauthenticated session, nor on a proof other than the one whose opening
was checked (type). The bare Polygero `verify` of tests checks the opening
of its `Unverified` proof before that proof's seal.

**I11. Proof bytes hold only prover data.** One version magic at the
outermost layer (`MDA7` for mdoc). The proof contains no nested magic and no
setup constants.
*Enforced by:* a test that the proof length equals the length the geometry and
the drawn column indices determine, the frontier counted from the indices
independently of either role (the standalone test in `zk/tests.rs`).

## Byte grammar

Strands and PRF blocks: each node starts with
`u32(STRAND) || u64(id) || u32(parents) || parent`, where the root has id 0
and no parent and each continuation has one parent and the next id. PRF
blocks hash `u32(PRF) || u64(id) || parent || u64(counter)`. The node payload
is:

```text
; every integer is u64 little endian
node      := message+ end
message   := tag value{arity(tag)}           ; arity and kinds fixed per tag (I6)
value     := 0  count byte{count}             ; Bytes
           | 1  count u64{count}              ; Nats
           | 2  field count elem{count}       ; Elements: registered FieldID, then canonical serialization
           | 3  count byte{ceil(count/8)}     ; Bits: LSB first, zero padding
field     := 1                                ; P-256: elem is 32 bytes
           | 4                                ; GF(2^128): elem is 16 bytes
end       := 0                                ; ROUND: a draw follows
           | 1                                ; SEAL: the proof ends
tag       := 16 ..                            ; 0..15 reserved for terminators
```

Parsing needs only the registry and the registered fields: read a u64. A
value below 16 ends the node; otherwise it names a tag whose arity says how
many self-delimiting values follow. The whole transcript is therefore an
injective encoding of the sequence of messages and boundaries, which Lean
proves once: the deployed points' injectivity follows from the grammar's
(`TaggedGrammar.toPoint_injective`).

## Statement

The statement is everything the verifier fixes before it reads a proof byte,
in three groups: identity, geometry, public inputs. It is a fixed sequence of
messages at the start of the first node, each with a fixed arity. Every
circuit public input is in the statement, including values the verifier could
derive from other statement values, such as the device-authentication digest
`e2`; the rule is checkable at a glance.

| Group | Message | Values | Source |
|---|---|---|---|
| Identity | `MdocStatement` | Bytes protocol ID; Bytes session transcript; Bytes(32) combined hash; Nats(version, attribute count) | `ZkSpecStruct`, application context |
| Identity, geometry | `Circuit` | Bytes(32) circuit ID, which hashes the circuit's field, its output, input and public input counts and each layer's width | one per circuit in participant order: hash circuit, adapter fragment, signature circuit |
| Geometry | `CommitmentLayout` | Nats(FieldID, committed private inputs before packing, pad cells, fingerprint mask cells); Bytes packing descriptor (it carries the packing degree); Nats(native runs as consecutive (first, count, cell) triples); Nats(bit-stored runs as consecutive (first, count, start, width) quadruples); Nats(mask start, mask width) | one per field participant: binary, then prime |
| Geometry | `AdapterLayout` | Bytes adapter mode ID (`longfellow/v2/foreign/p256/two-full-field-trees/v1` for the P-256 adapter); Nats(quotient bits Q, tree count, virtual leaves per tree); Nats(start and width of each quotient pad among the binary private inputs; R's bits are in the split participant's `CommitmentLayout`) | one per adapter; written by the mode from its geometry, whose type parameter Q must equal the absorbed Q |
| Geometry | `JointGeometry` | Nats(k, s, n, t), the proof's one Polygero profile; each field's committed cell count nw follows from its `CommitmentLayout` | `ComposedGeometry::config` |
| Public inputs | `PublicInputs` | Elements(GF2_128, 901 + 788A) for the hash circuit with A attributes; Elements(P256, 258) for the signature circuit (pkx, pky, then the 256 bits of e2 as 0/1, least significant first) | one per field: `PublicInputs::derive` |

The protocol ID names the statement type: `longfellow/v2/mdoc/transcript/v2`
for `MdocStatement` and `longfellow/v2/zk/transcript/v2` for `ZkStatement`.
Public inputs are absorbed as the circuit sees them: field elements of the
circuit's field, so every field's public inputs have one representation.

The geometry messages are written from the same `ComposedGeometry` and layout
objects the verifier uses to parse the proof (I2), so the absorbed geometry
and the checked geometry cannot differ. A standalone ZK proof
(`ZkProofStatement`) starts with `ZkStatement` (protocol ID, context) and
then the same `Circuit`, `CommitmentLayout`, `JointGeometry` and
`PublicInputs` messages. Alone, `ZkStatement` is the whole statement of a
bare transcript (`Transcript::for_test`, for tests and tools), which has no
Polygero profile.

## Message registry

Tag ranges group the messages by owning component. `F` is the sending
component's field.

| Tag | Message | Sent by | Values |
|---|---|---|---|
| 16 | `MdocStatement` | statement | see Statement |
| 17 | `ZkStatement` | statement | Bytes protocol ID, Bytes context |
| 18 | `Circuit` | statement, one per circuit | Bytes(32) circuit ID |
| 19 | `CommitmentLayout` | statement, one per field | Nats(4), Bytes, Nats (native run triples), Nats (bit-stored run quadruples), Nats(2) |
| 20 | `JointGeometry` | statement | Nats(4) |
| 22 | `AdapterLayout` | statement, one per adapter | Bytes, Nats(3), Nats |
| 21 | `PublicInputs` | statement, one per field | Elements(F, n): the circuit's public inputs |
| 32 | `Commitment` | joint Polygero; it is witness selection's opening message | Bytes(32) root |
| 33 | `FingerprintResponse` | witness selection, one per field | Elements(F, 2) |
| 48 | `SumcheckRound` | sumcheck | Elements(F, 2): c0-s0, c1-s1 |
| 49 | `SumcheckCross` | sumcheck | Elements(F, 1) |
| 50 | `SumcheckClaims` | sumcheck | Elements(F, 2) |
| 64 | `SplitOpening` | split | Elements(P256, 1): mu |
| 65 | `P256AdapterQuotients` | P-256 adapter | Bits(Q), Bits(Q): the two masked quotient words |
| 80 | `PackingU` | dual packing | Elements(F, m), m the packing degree |
| 81 | `PackingA` | dual packing | Elements(F, 1) |
| 96 | `PolygeroResponse` | Polygero, one per committing field | Elements(F, k+s): H, Elements(F, 2k): Z |
| 112 | `Seal` | complete-proof encoder | Bytes: every proof byte before the seal block, magic included |

Terminal, absorbed only by the seal: Polygero rows (u, m, witness, f*),
Merkle nonces, the frontier count and the Merkle frontier.

## Challenge schedule

Each row is one boundary: the messages that close the node, then the draws
read from its stream, in read order. Draws marked *leading* are made by the
next sub-protocol on entry, before its first message (I8).

| Node closes after | Draws, in order | Consumer |
|---|---|---|
| Statement messages, `Commitment` | 2 x Elements(GF2_128, cells), 2 x Elements(P256, cells) | witness selection |
| `FingerprintResponse` x 2 | prime top weights (*leading*) | prime sumcheck |
| `SumcheckRound` | z | sumcheck |
| `SumcheckCross` | r != 0 | sumcheck |
| `SumcheckClaims` | alpha; then the next stage's weights (entering outputs, then quadratic assertions, then linear assertions), or the input assertions at the last stage; after the prime frontend's last layer also eta != 0 (*leading*) | sumcheck; split |
| `SplitOpening` | conversion pair, each != 0 (*leading*) | adapter |
| `P256AdapterQuotients` | host top weights (*leading*) | host sumcheck |
| `PackingU` | m independent `elements(F)`, m the packing degree | dual packing |
| `PackingA` | Polygero batching weights (drawn and used by the joint opening): per field, one weight per equation, then s+1 samples per batched row | Polygero |
| `PolygeroResponse` x 2 | t distinct column indices out of n | Polygero |
| `Seal` | seal block | proof encoder |

**Boundary count.** Sumcheck rounds (the sum of the layers' log-widths, one
round each), plus 2 per layer (cross, claims), plus 7 others; the seal is
not counted. A participant whose packing degree is one sends no packing
messages and has no packing boundaries; the next draws then read further
from the preceding node (I7). Likewise a sumcheck with zero layers sends
nothing after its top weights, which are its input assertions, and the
draws after it read further from the node that precedes it; a zero-layer
frontend of packing degree above one still sends its packing messages.
Pure-foreign storage (no native cells) adds its row weights, drawn by the
pure split step at the frontend's last boundary, before the conversion pair. The four
supported mdoc shapes (one to four attributes) have 457/461/466/469
boundaries; four attributes: 400 + 2 x 31 + 7 = 469. The boundary count
enters the soundness bound only as r/2^256.

### Draw kinds

- `element(F)` (`Reading::elt_field`): GF(2^128) reads 16 bytes. A prime
  field reads its sample byte count, masks the top byte and rejects values at
  or above the modulus.
- `nonzero(F)` (`Reading::nonzero`): `element` repeated until nonzero.
- `elements(F, n)` (`Reading::elements`): n independent elements in order,
  yielded lazily to the caller, who stores them where it keeps them.
- `indices(n, out)` (`Reading::choose(out, n, scratch)`): `out.len()`
  distinct indices out of 0..n, by Fisher–Yates with masked rejection in the
  caller's scratch.

These four are the only ways to read a stream outside tests, and none of
them allocates. Raw bytes are test-only.

## Rust API

```rust
// runtime::v2::transcript
// The statement: its identity message, then the rest (I1).
pub trait Statement {
    type Identity: SetupMessage + ?Sized;
    fn identity(&self) -> &Self::Identity;
    fn write(&self, h: &mut Header<'_>);           // Header::send takes only SetupMessages
}
// A session: a transcript and the statement that opened it (I1, I2).
pub struct Opened<'s, S: ?Sized> { statement: &'s S, transcript: Transcript }
impl<'s, S: Statement + ?Sized> Opened<'s, S> {
    pub fn new(statement: &'s S) -> Self;          // absorbs S as the first messages (I1)
}
impl<'s, S: ?Sized> Opened<'s, S> {
    pub fn statement(&self) -> &'s S;
    pub(crate) fn bound<P: ?Sized + 's>(&mut self, f: impl FnOnce(&'s S) -> &'s P) -> Bound<'_, P>;
}
// named accessors (I2), in runtime::v2::zk and runtime::v2::foreign::compose
impl Opened<'_, ZkProofStatement<'_, F>> { pub fn geometry(&mut self) -> Bound<'_, ZkProofGeometry>; }
impl Opened<'_, ComposedStatement<'_, ..>> { pub(crate) fn geometry(&mut self) -> Bound<'_, ComposedGeometry>; }
// public only in testonly builds, for bare sessions (`for_test`); elsewhere
// crate-private, and every session outside the crate is an `Opened`'s
pub struct Transcript { .. }
impl Transcript {
    pub(crate) fn new<S: Statement + ?Sized>(statement: &S) -> Self;
    pub(crate) fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P>;
    #[cfg(feature = "testonly")]
    pub fn bound_for_test<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P>;
    pub(crate) fn append_final_seal(self, body: Vec<u8>) -> EncodedProof; // I10
    // I10; called only after an opening check (zk::Authenticated::check_seal)
    pub(in crate::runtime::v2) fn check_seal<P>(self, proof: Unverified<'_, P>)
        -> Result<VerifiedProof, &'static str>;
}
pub struct Bound<'a, P: ?Sized> { part: &'a P, owner: &'a mut Transcript }
impl<'a, P: ?Sized> Bound<'a, P> {
    pub fn part(&self) -> &'a P;
    pub fn session(&self) -> SessionStamp;
    pub(crate) fn project<Q: ?Sized + 'a>(&mut self, f: impl FnOnce(&'a P) -> &'a Q) -> Bound<'_, Q>;
    pub(crate) fn transcript(&mut self) -> TranscriptRef<'_>;
}
impl TranscriptRef<'_> {
    pub(crate) fn send<M: ProverMessage + ?Sized>(&mut self, m: &M);           // I4
    pub(crate) fn draw<T>(&mut self, f: impl FnOnce(&mut Reading<'_>) -> T) -> T; // I7
}
// A message with field elements holds a reference to its field.
pub trait Message { const TAG: Tag; fn encode(&self, e: &mut Encoder<'_>); }
pub trait ProverMessage: Message {}
pub trait SetupMessage: Message {}
impl Encoder<'_> {                                     // I5: the only writer
    pub fn bytes(&mut self, b: &[u8]);
    pub fn nats(&mut self, xs: &[u64]);
    pub fn elements<F: RegisteredField>(&mut self, f: &F, xs: &[F::E]);
    pub fn bits(&mut self, bits: impl ExactSizeIterator<Item = bool>);
}
impl<'a> Reading<'a> {                                 // the four draw kinds
    pub fn elt_field<F: SupportsSampling>(&mut self, f: &F) -> F::E;
    pub fn nonzero<F: SupportsSampling>(&mut self, f: &F) -> F::E;
    pub fn elements<'r, F: SupportsSampling>(&'r mut self, f: &'r F, n: usize)
        -> impl Iterator<Item = F::E> + use<'r, 'a, F>;
    pub fn choose(&mut self, out: &mut [usize], n: usize, scratch: &mut [usize]);
}

// the proof is parsed against the absorbed geometry (I2)
impl MdocProof {
    pub fn read<'a>(bytes: &'a [u8], g: &Bound<'_, ComposedGeometry>, f1: &F1, f2: &F2)
        -> Result<Unverified<'a, Self>, String>;
}
impl ZkProof<F> {
    pub fn read<'a>(bytes: &'a [u8], g: &Bound<'_, ZkProofGeometry>, f: &F)
        -> std::io::Result<Unverified<'a, Self>>;
}

// a frontend draws its top weights on entry (I8); runtime::v2::zk, crate-private
pub(crate) fn prove(t: &mut Bound<'_, FrontendPart<'_, F>>, state: CircuitState<F>,
    virtual_inputs: &VirtualInputs<F::E>) -> Result<(CircuitProof<F>, LinearStatement<F::E>), String>;
```

A leading challenge is drawn inside the call that consumes it, after the
calls whose messages it follows have returned. It cannot be drawn too early
(the host frontend call, which draws the host top weights, takes the leaves
that the adapter call returns after sending its quotients), drawn from
another transcript, or reused. The transcript itself decides whether a draw
opens a node (I7), so callers never manage rounds.

`Opened::new` is the only way to open a transcript outside the crate. Prove
and verify entry points take an `Opened` session or the statement itself
(`ZkProver::commit` opens its own session), never a statement and a
transcript separately, so a proof cannot be checked against a statement other
than the one its transcript absorbed.

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Using a public input or circuit that was never absorbed | I2: components have no parameter for them |
| Choosing part of the statement after a challenge | I1: the statement exists before the transcript does |
| Absorbing a circuit ID or geometry value a second time | I3: setup messages (`SetupMessage`) can only be written by the statement |
| Verifying against a geometry other than the one absorbed | I2: the proof reader and every component take geometry from a `Bound` that only the statement's accessors build |
| Drawing a sub-protocol's first challenge before the message it depends on | I8: the sub-protocol draws it on entry, and takes what it depends on as arguments; the role-trace test and the golden vectors pin the drivers' order |
| Reusing one challenge for two frontends | I8: each frontend draws its own on entry |
| Batching a system other than the one the weights were drawn for | I8: the batching weights are internal to the joint opening, which draws them for the equations it takes |
| Holding a challenge across a message | I8: no challenge leaves the call that draws it |
| A round with no prover message | I7: cannot be expressed |
| Interleaving one field's statement with another field's batching challenges | Statements are derived (I3); batching draws follow `PackingA`, after every frontend message |
| An element absorbed as the wrong field | I5: Elements carry the FieldID of a `RegisteredField`, which names one field and one width |
| Prover and verifier drifting apart | I9: trace equality test |
| Two messages with the same tag, or one tag with two layouts | I6: the compiler, the exhaustive `Tag::schema` and the trace checks |
