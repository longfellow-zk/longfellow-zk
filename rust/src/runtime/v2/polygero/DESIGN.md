# Polygero design

Polygero is the v2 polynomial commitment and linear-statement proof. It
commits to one witness vector per field in a single Merkle tree of columns,
and then proves for each field `F` a linear system `A_F*w_F + b_F = 0` over
`F`. The mdoc proof has two fields: GF(2^128) for the binary host (hash
circuit) and the P-256 base field `P256Field` for the split participant
(signature circuit). Polygero opens first and closes last. Its `Commitment`
message follows the statement directly and is also witness selection's
opening message. Witness selection and the frontends (sumcheck,
split, adapter, dual packing) then run on the same transcript and derive each
field's linear system from their messages and challenges. Polygero's
response phase takes those systems, draws its batching weights and uses them
at once, sends one response per field, opens one shared set of columns, and
hands the transcript to the seal (transcript I10). The column
tree is the v2 Merkle commitment (`runtime/v2/merkle/DESIGN.md`).

Code comments and other design documents cite the invariants below as
"Polygero I1" and so on, and the transcript invariants as "transcript I1".

## Parameters and geometry

The application chooses four dimensions, `PolygeroConfig { k, s, n, t }`
(`runtime/v2/proto/polygero.rs`). Each field adds its witness count `nw`;
`PolygeroGeometry::new(nw, config)` validates the five values.

| Symbol | Meaning | Derived counts |
|---|---|---|
| `k` | Row dimension: every ordinary row has degree below `k` | `\|Z\| = 2k` |
| `s` | Batching degree: each `B_i` has degree at most `s` | `\|H\| = k+s` |
| `n` | Committed columns (Merkle leaves) | |
| `t` | Opened columns, and random prefix samples per witness row | opened values per field `t*nrow` |
| `nw` | Witness count of one field | `data_rows = ceil(nw/(k-t))`, `nrow = data_rows + 3` |

`PolygeroGeometry::validate` requires every one of `nw, k, s, n, t` to be at
most `MAX_SIZE = 2^28`, `k >= 1`, `1 <= t < k`, `t <= n`, `k+s <= n`,
`2k <= n`, and `nrow*n <= 2^28`. All participants of one joint commitment
share `(k, s, n, t)`; their fields and `nw` may differ.

**Evaluation points.** Each field has an ordered evaluation domain
`x_0, x_1, ...` (`EvaluationDomain`, identified by `domain_id()`). Points
`0..k` are logical slots; points `k..k+n` are the oracle, and column `j`
holds every row's value at `x_{k+j}`. `PolygeroConfig::can_interpolate`
checks that the backend supports every interpolation the protocol uses:

| Source points | Destination | Use |
|---|---|---|
| `0..k` | oracle | witness rows, `m`, selector `z_R`, verifier `C_i` |
| `0..k+1` | oracle | vanishing polynomial `V` |
| `0..k` | `k..3k` | prover `C_i` on Z's points |
| `k..2k` | oracle | free mask `u` |
| `k..2k+s` | oracle | `f*`, and the verifier's extension of `H` |
| `k..k+s+1` | `k..2k+s` | `B_i` at H's points |
| `k..k+s+1` | oracle | `B_i` at the opened columns |
| `k..3k` | `0..k+n` | `Z` for the prefix, sum and column checks |

**Row layout.** Rows are ordered `u, m`, the data rows, then `f*`
(`PolygeroParam::u_row`, `m_row`, `data_start`, `fstar_row`). Every row is
stored as its evaluations on the oracle.

| Row | Index | Specified by | Degree | Randomness |
|---|---|---|---|---|
| `u` | 0 | `k` samples at `x_k..x_{2k}` | `< k` | all `k` uniform |
| `m` | 1 | `k` samples at `x_0..x_k` | `< k` | uniform, except `m[t] = -sum_{j>t} m[j]`, so `sum_{j=t}^{k-1} m(x_j) = 0` |
| data row `i` | `2+i` | `k` samples at `x_0..x_k`: `t` masks, then `w[i*(k-t) ..]`, zero padded | `< k` | first `t` uniform |
| `f*` | `nrow-1` | `k+s` samples at `x_k..x_{2k+s}` | `< k+s` | all uniform |

All masks are uniform in the participant's field, also for rows that carry
base-field values such as bits.

**mdoc profile.** `MDOC_JOINT_PROFILE = (349, 12, 2443, 84)`
(`mdoc/proto/config.rs`), certified by `zk_tool check-profiles`. It gives
row width 265, `|H| = 361`, `|Z| = 698` and a Merkle heap of depth 12.

## Statement

**Starting claim.** The transcript statement fixes one Polygero profile
`(k, s, n, t)` for the whole proof in `JointGeometry`, and the witness count
`nw` of each committing field, in participant order, follows from that
field's `CommitmentLayout` (transcript I1, I3). The prover holds `w_F` in
`F^nw_F` for each field.

**Committed.** The rows of every field, through one Merkle root over `n`
columns. A column holds, for every participant in tuple order, that
participant's `nrow` row values at one oracle point.

**Derived.** After the commitment, each field's frontend derives `m_F`
affine equations `A_F*w_F + b_F = 0` from absorbed messages and challenges
(`LinearStatement { a, b, session }`, stamped with the session that derived
it). `A_F` is sparse: a list of terms
`PolygeroLinearTerm { c, w, k }` that add `k*w[w]` to equation `c`; repeated
`(c, w)` entries add. Equation and witness indices satisfy `c < m_F` and
`w < nw_F`. Production statements are always derived. A static system that
no frontend derives exists only in tests and tooling (`testonly`,
`tooling`); it is not bound by the transcript and has no statement message.

**Final claim.** Polygero reduces nothing further. The verifier accepts only
if, for every field, the rows behind the root are close to codewords whose
decoded witness satisfies `A_F*w_F + b_F = 0`, except with the soundness error
below. Public: the root, H and Z of every field, the opened columns, their
nonces and frontier. Secret: everything else in the rows.

## Invariants

**I1. One geometry and one query set for every field.** A proof has one
Polygero profile, and all participants share its `(k, s, n, t)`, so one
column index addresses a column in every field and one Merkle leaf holds all
of them. Fields keep their own arithmetic, witness count and equation count.
*Enforced by:* `JointPolygeroParam::new` rejects a tuple whose participants
differ in `(k, s, n, t)` ("joint geometry mismatch") or is empty; prover and
verifier exist only for a `JointPolygeroParam` (type).

**I2. The proof shape is a function of the absorbed geometry.** H has `k+s`
elements, Z has `2k`, each field has `t*nrow` opened values, and there are
`t` nonces. The frontier is a u64 count `d` of digests, at most
`t*(ceil(log2 n)+1)`, then the `d` digests; it ends the body. The complete
reader takes the geometry from the `Bound` part the statement wrote.
Polygero's part of the body holds prover data only: no version magic,
context or setup constant, and no integer but the frontier count
(transcript I11).
*Enforced by:* the complete readers take `&Bound<'_, G>`, and the Polygero
body readers are crate-private (type, proto I2); `checked_body` checks the
whole length, the frontier count included, before anything is allocated
(runtime); the transcript I11 proof-length test.

**I3. Every field's statement is fixed before any batching challenge.** The
statements are derived from messages already absorbed, so nothing is absorbed
for them (transcript I3). The prover's `prove` and the verifier's `reduce`
take every field's statement, called after the last frontend message. They
validate the statements, then draw the batching weights of all fields at that
boundary (`JointPolygeroParam::weights_for`, crate-private) for exactly the
statements' equation counts, and consume them in the same call, before the
response phase sends its first message, `PolygeroResponse`. The weights are
internal to that call (transcript I8): no caller holds them, so none can
pair them with another system or carry them past a message.
*Enforced by:* `prove` and `reduce` draw the weights themselves from the
statements they are given, and no public item returns or accepts them
(type); the test
`batching_follows_the_absorbed_messages_and_precedes_the_responses`.

**I4. Every response is sent before the one query draw.** Both roles send
`PolygeroResponse` for every field in tuple order, then draw the `t` column
indices. A commitment is opened exactly once, on the transcript that received
it: the prover and verifier states record the session stamp at `commit` and
`receive` and check it in `prove` and `reduce` (transcript I2).
The masking has zero slack: each row has exactly `t` random prefix samples
for the `t` opened columns (I7), so one more opened column of the same
commitment, by a second query draw, a retry or a debugging opening, breaks
zero knowledge. A commitment answers one query draw of `t` columns and
nothing else.
*Enforced by:* the shared schedule in `polygero/transcript.rs`, called by
both roles (transcript I9); `JointPolygeroProver::prove` consumes the prover,
which is not `Clone` (type); the session stamp check (runtime; test
`prover_and_verifier_states_complete_only_on_their_own_session`).

**I5. Opened values are authenticated before they are used.** The verifier
rebuilds each opened leaf from the proof's rows and nonce at the drawn column
and checks the root before any field equation reads those values.
*Enforced by:* the verifier's opening check,
`JointPolygeroVerifier::reduce`, which complete proofs run inside their
composition, calls `merkle::verify_proof` before `Participants::check`
(runtime); the test
`joint_authenticates_every_field_response_column_and_opening`.

**I6. Each field's checks run in that field only.** Shared queries correlate
the fields' checks; they never combine values of two fields. Participants are
typed `(Participant, Tail)` tuples ending in `()`; witnesses, statements,
challenges, responses and rows have the same tuple shape.
*Enforced by:* the sealed `Participants` trait and its associated types
(type).

**I7. Masks come from private randomness only.** Every mask sample (`u`,
`m`, `f*`, the `t` prefix samples of each data row) and every Merkle nonce
is drawn from the prover's `PrivateRandom`, never from the transcript.
Witness validation happens before any of it is drawn.
The `t` prefix samples hide exactly the `t` opened columns, with no margin:
the counting argument balances at `t` openings and fails at `t + 1`, so no
extra opening of a committed row is allowed (I4).
*Enforced by:* `encode_rows` and `ColumnOracle::new` take
`&mut impl PrivateRandom` (type); the test
`participant_order_and_late_errors_are_bound_before_sampling`.

**I8. The verifier's checks are exactly the four equations below.** For each
field: the primary response check, the zero prefix of Z, the global sum, and
the arithmetic column check. Each is a pure function of the public geometry,
the statement, the challenges, H, Z and the authenticated columns.
*Enforced by:* `verifier::check_response` (runtime); the reference
implementation in `polygero/tests/reference.rs`; the Lean verifier
`RecursivePolygero.Local.Polygero.verify` and `LfzkV2.Current.BackendPrefix.Zero`.

## Protocol

Polygero sends and draws the following, in order. `P` is the participant
count, `F` the participant's field, `m_F` its equation count and `nrow_F` its
row count. Tags are from the transcript registry.

| Step | Who | Message or draw | Values | Size |
|---|---|---|---|---|
| 1 | prover | `Commitment` (32) | Bytes(32): Merkle root | 32 bytes |
| | | *frontends run* | | |
| 2 | draw | batching, per field in tuple order | `elements(F, m_F)`: alpha; then for each row `i` in `0..nrow_F-1`: `elements(F, s+1)`: samples of `B_i` at `x_k..x_{k+s+1}` | `m_F + (nrow_F-1)(s+1)` elements |
| 3 | prover | `PolygeroResponse` (96), once per field in tuple order | Elements(F, k+s): H; Elements(F, 2k): Z | `3k+s` elements |
| 4 | draw | queries | `indices(n, out)` (`Reading::choose`) with `out.len() = t`: distinct columns, in draw order | `t` indices |
| 5 | prover | terminal, the tail of the body | rows of each field, nonces, frontier count, frontier | see Formats |

Step 1 closes the first node together with the statement. Step 2 reads from
the boundary after the last frontend message: `PackingA` in mdoc, the last
`SumcheckClaims` when no participant packs (its stream continues, transcript
I7), `Commitment` when no frontend runs. Steps 3 and 4 form one boundary.
Step 5 is covered only by the seal (transcript I4).

**Prover.** `commit` validates the witnesses, encodes the rows of every
field, samples one 32-byte nonce per column, and builds the Merkle tree over
the `n` leaves. `prove` draws the batching challenge and computes, per
field:

```text
H = f* + sum_{i in 0..nrow-1} B_i * W_i                on x_k .. x_{2k+s}
C_i(x_j) = 0 for j < t;  a(i*(k-t) + j - t) for t <= j < k  (0 past nw)
  where a(w) = sum over terms (c, w, coeff) of alpha_c * coeff
Z = sum_{data rows i} C_i * W_{2+i} + V * u + z_R * m  on x_k .. x_{3k}
```

`V` is the monic polynomial vanishing on `x_0..x_k`; `z_R` is zero on
`x_0..x_t` and one on `x_t..x_k` (`polynomials.rs`). It sends the responses,
draws the queries, and gathers the opened rows and nonces in query order.

**Verifier.** After reading the proof against the absorbed geometry, it
draws the batching challenge, absorbs the responses, draws the queries and
checks, in this order:

1. Merkle: for each query `q` at column `j_q`, the leaf hash of nonce `q` and
   the opened values `q` of every field, in tuple order; `verify_proof` with
   `n` leaves against the root and the frontier (Merkle I6, I7).
2. Primary, per field: extend H from `x_k..x_{2k+s}` to the oracle, and for
   every query `q` at column `j = j_q`
   `H(x_{k+j}) = f*_q + sum_{i in 0..nrow-1} B_i(x_{k+j}) * W_{i,q}`.
3. Zero prefix: extend Z from `x_k..x_{3k}` to `x_0..x_{k+n}`;
   `Z(x_j) = 0` for `j < t`.
4. Global sum: `sum_{j=t}^{k-1} Z(x_j) + sum_c alpha_c * b_c = 0`.
5. Arithmetic column, for every query `q` at column `j = j_q`:
   `Z(x_{k+j}) = sum_i C_i(x_{k+j}) W_{2+i,q} + V(x_{k+j}) u_q + z_R(x_{k+j}) m_q`.

Any failure rejects with a `PolygeroError`.

## Formats

All integers are u64 little endian. Field elements use their canonical
serialization (`SerializableField`, 16 bytes for GF(2^128), 32 bytes for
P-256); the reader rejects non-canonical encodings (`proto::read_field`).
The enclosing proof body lists every interactive field in send order, then
the terminal fields. Polygero's interactive fields are the root and the
responses, at their send positions; its terminal fields form the tail of the
body:

```text
; interactive, at their send positions
commitment := digest                             ; Commitment: the first body field
response   := elem{k+s} elem{2k}                 ; PolygeroResponse: H, Z; one per field, tuple order
; terminal, the end of the body, in this order
terminal   := field_rows{P} nonce{t} frontier
field_rows := row{nrow}                          ; per field, tuple order; rows u, m, data rows, f*
row        := elem{t}                            ; one row's values, in query order
nonce      := byte{32}                           ; in query order
frontier   := u64(d) digest{d}                   ; the end of the body, decreasing heap index
digest     := byte{32}
```

The frontier states its digest count `d` in one u64 word. Before parsing
anything, the complete reader checks once that the body has exactly the
length its fixed-size fields, the count word and `d` digests need, with
`d <= t*(ceil(log2 n)+1)` (`checked_body`, proto I3); nothing may follow the
frontier. `verify_proof` then requires the exact canonical count (Merkle I7).

Sizes: a field's response has `(3k + s) * |F|` bytes and its rows
`t*nrow * |F|` bytes; the authentication has `32t + 8 + 32d` bytes for `d`
frontier digests. For the mdoc profile, H and Z take 16944 bytes in
GF(2^128) and 33888 bytes in P-256, and the nonces take 2688 bytes.

**Merkle hash domain.** Leaf and node hashes use the fixed 32-byte domain
`DOMAIN` (`runtime/v2/merkle/hash.rs`), the label `longfellow/v2/merkle/domain` zero-padded
(Merkle I3). The parameters that fix the tree's shape and the leaf layout
are bound by the transcript statement (transcript I3), so no digest of them
is computed.

**Leaf column bytes.** The Merkle leaf for column `j` appends, after its
fixed header (Merkle I1), for each participant in tuple order and each row in
row order, the canonical encoding of that row's value at `x_{k+j}`. Widths
and row counts follow from the statement, so no separators are needed.

## Rust API

```rust
// runtime::v2::proto::polygero: the prover/verifier contract
pub struct PolygeroConfig { pub k: usize, pub s: usize, pub n: usize, pub t: usize }
pub struct PolygeroGeometry { /* nw, k, s, n, t: crate-private */ }
impl PolygeroGeometry {
    pub fn new(nw: usize, config: PolygeroConfig) -> io::Result<Self>;
    pub fn config(&self) -> PolygeroConfig;
    pub fn validate(&self) -> io::Result<()>;
    pub fn nrow(&self) -> usize;                    // ceil(nw/(k-t)) + 3
    pub fn response_lengths(&self) -> [usize; 2];   // [k+s, 2k]
}
pub struct PolygeroCommitment { /* root: Digest */ }
pub struct FieldProof<E> { /* h: k+s, z: 2k (PolygeroResponse); rows: t*nrow (terminal) */ }
pub struct JointPolygeroProof<B> { /* bodies: B, opening: MerkleProof */ }  // B: (FieldProof<E>, tail)
impl<B> JointPolygeroProof<B> {
    pub fn bodies(&self) -> &B;
    pub fn authentication_bytes(&self) -> (usize, usize);  // nonces, frontier with its count
}
// The body codec is crate-private: the complete readers and writers
// (proto::zk, proto::composed) call FieldProof::{read_response, read_rows,
// write_response, write_rows} and JointPolygeroProof::{read, write_to_buf}
// at their send positions (I2, proto I2).

// runtime::v2::polygero
pub struct PolygeroParam { /* geometry, domain id */ }
impl PolygeroParam {
    pub fn try_new<const W: usize, F, D: EvaluationDomain<W, F>>(
        nw: usize, config: PolygeroConfig, domain: &D,
    ) -> Result<Self, PolygeroError>;               // geometry and interpolation capacity
    pub fn geometry(&self) -> PolygeroGeometry;
}
pub struct Participant<'a, const W: usize, F, D> { /* param, &'a F, &'a D */ }
impl<'a, const W: usize, F, D> Participant<'a, W, F, D> {
    pub fn new(param: PolygeroParam, domain: &'a D) -> Result<Self, PolygeroError>;
}
pub trait Participants: Sealed {                    // (), (Participant, Tail): I6
    type Witnesses; type Statements; type States; type Bodies; type Challenges;
    ..                                              // States: prover builds only
}
pub struct JointPolygeroParam<L: Participants> { /* participants, config */ }
impl<L: Participants> JointPolygeroParam<L> {
    pub fn new(participants: L) -> Result<Self, PolygeroError>;   // I1
    pub fn config(&self) -> PolygeroConfig;
    // I3: called by prove and reduce only, for the statements they take
    pub(super) fn weights_for(&self, statements: &L::Statements,
        t: &mut TranscriptRef<'_>) -> L::Challenges;
}
// fields crate-private: a: Vec<PolygeroLinearTerm<E>>, b: Vec<E>, session: SessionStamp
pub struct LinearStatement<E> { .. }
pub struct PolygeroLinearTerm<E> { pub c: usize, pub w: usize, pub k: E }

// One field's encoded rows and the geometry they were encoded for (prover).
pub struct FieldState<E> { /* geom: PolygeroGeometry, rows: Vec<Vec<E>> */ }
pub struct JointPolygeroProver<S> { /* session stamp, states, column oracle; not Clone */ }
impl<S> JointPolygeroProver<S> {
    pub fn commit<L: Participants<States = S>>(
        t: &mut Bound<'_, JointPolygeroParam<L>>,
        witnesses: L::Witnesses,                    // moved: released before Merkle construction
        rng: &mut impl PrivateRandom,               // I7
    ) -> Result<(Self, PolygeroCommitment), PolygeroError>;      // sends Commitment
    pub fn prove<L: Participants<States = S>>(
        self,                                       // I4: one opening per commitment
        t: &mut Bound<'_, JointPolygeroParam<L>>,   // checked against the stamp
        statements: L::Statements,                  // I3: the weights are drawn here
    ) -> Result<JointPolygeroProof<L::Bodies>, PolygeroError>;
}
pub struct JointPolygeroVerifier<L: Participants> { /* session stamp, root */ }
impl<L: Participants> JointPolygeroVerifier<L> {
    pub fn receive(t: &mut Bound<'_, JointPolygeroParam<L>>, root: &PolygeroCommitment) -> Self;
    pub(crate) fn reduce(
        self,
        t: &mut Bound<'_, JointPolygeroParam<L>>,   // checked against the stamp
        statements: L::Statements,                  // I3: the weights are drawn here
        proof: &JointPolygeroProof<L::Bodies>,
    ) -> Result<(), PolygeroError>;                 // the opening check; the caller checks the seal
}

// tests and tools only: #[cfg(any(test, feature = "testonly", feature = "tooling"))]
impl<E> LinearStatement<E> {
    pub fn new(a: Vec<PolygeroLinearTerm<E>>, b: Vec<E>) -> Self;  // static system, no session
}
impl<L: Participants> JointPolygeroParam<L> {
    pub fn write(&self, p: &JointPolygeroProof<L::Bodies>, transcript: Transcript)
        -> Result<EncodedProof, PolygeroError>;     // sealed bare body, no magic
    pub fn read<'a>(&self, bytes: &mut &'a [u8])
        -> Result<Unverified<'a, JointPolygeroProof<L::Bodies>>, PolygeroError>;
}
impl<L: Participants> JointPolygeroVerifier<L> {
    pub fn verify(self, transcript: Transcript, param: &JointPolygeroParam<L>,
                  statements: L::Statements,
                  proof: Unverified<'_, JointPolygeroProof<L::Bodies>>)
        -> Result<VerifiedProof, PolygeroError>;
}
```

The caller passes the statements to `prove` or `reduce` at the boundary
after its last message; they draw the batching weights there, from the
equation count of each statement, and use them at once. In the zk layer,
`JointProver::finish` and `JointVerifier::finish` do this for complete
proofs, after witness selection attaches its fingerprint equations.
`commit` and `receive` record the session stamp of their `Bound`; `prove` and `reduce` reject a
`Bound` with another stamp, so a prover or verifier state cannot be
completed on another transcript. Each field's prover state (`FieldState`)
records the full `PolygeroGeometry` its rows were encoded for, and `prove`
compares it with the parameter's (`Participants::validate_states`), so
opening with another parameter fails cleanly, even one with the same row
count and width (another `nw` can give the same rows). In production
`LinearStatement` has no public constructor: frontends build it inside
`runtime::v2` from their absorbed messages, stamped with the session they
derive on. `LinearStatement::new` exists only under `test`, `testonly` or
`tooling`, and so do the bare body codec (`JointPolygeroParam::write` and
`read`) and standalone `JointPolygeroVerifier::verify`. Its system belongs to
no session, so the zk layer's `finish` rejects it; the bare `prove` and
`reduce` ignore the stamp. Complete proofs encode the joint
body inside their own envelope (`proto::zk`, mdoc) and run the crate-private
opening check `reduce` before checking their own seal. The prover and
verifier never see a geometry, context or statement that is not reachable
from their `Bound` part.

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Choosing one field's statement after another field's batching challenges | I3: all statements are handed over together, and the one batching draw follows |
| Drawing batching challenges before the last frontend message | I3: they are drawn where the statements are handed over, after every frontend message that derives them |
| Batching weights drawn for another statement shape | I3: `prove` and `reduce` draw them for the equation counts of the statements they take |
| Opening a system other than the one the weights were drawn for | I3: the weights are drawn and consumed in the call that takes the statements; no caller holds them |
| Drawing queries before every response is fixed | I4: the shared schedule sends all responses, then draws |
| Opening two query sets for one commitment | I4: `prove` consumes the prover; it is not `Clone` |
| Completing a prover or verifier state on another transcript | I4: session stamp recorded at `commit`/`receive`, checked in `prove`/`reduce` |
| Two fields with different `n` or `t` in one tree | I1: `JointPolygeroParam::new` rejects them |
| Parsing with a geometry other than the absorbed one | I2: the complete reader takes `Bound` |
| Reusing a root under another geometry or participant order | the statement binds both before the root is sent (transcript I3) |
| Opening a commitment with rows encoded for another parameter | `prove` compares the geometry each state recorded with the parameter's (`validate_states`) |
| Opened values at the wrong column | Merkle I2: the leaf binds its column index |
| Using an opened value before authentication | I5: Merkle check precedes field checks |
| Mixing two fields' arithmetic | I6: typed tuples, one field per participant |
| Masks predictable from the transcript | I7: masks take `PrivateRandom` only |
| A wrong witness length consuming randomness, or a bad constraint index reaching the checks | witness validation precedes sampling; statement validation precedes the responses; `participant_order_and_late_errors_are_bound_before_sampling` |
| Non-canonical element aliases in the proof | `read_field` re-encodes and compares |
| An oversized frontier forcing a large allocation | I2: one length check, with the frontier count capped, before parsing |
| An interpolation backend too small for the geometry | `can_interpolate` in `PolygeroParam::try_new` and `Participant::new` |
| A participant attached to a domain other than its parameter's | `Participant::new` compares `domain_id` |

## Soundness and zero knowledge

**Checks.**

| Check | Purpose |
|---|---|
| Merkle authentication | Binds the opened values to the rows fixed at commitment, so the extractor reads them from the commitment-time query table |
| Primary response (H) | Proximity: the random degree-`s` polynomials `B_i` fold every row into one word that must be a codeword of degree `< k+s` |
| Zero prefix of Z | Deterministic runtime check that Z vanishes on the mask slots (`LfzkV2.Current.BackendPrefix.Zero`); the paper verifier is unchanged |
| Global sum | The alpha-weighted sum of the equations holds on the decoded witness |
| Arithmetic column | Z agrees with `sum C_i W_i + V u + z_R m` at every opened column |
| `t` distinct queries | Catches columns where a far word disagrees with its decoding |

**Error terms.** The formal error for one recursive Polygero invocation is
`eps = theta + (1 - theta)(mu + 1/q)` with
`mu = choose(n, k+2s+1)/q^(s+1)` (`formal/polygero/README.md`,
`RecursivePolygero.Protocol.ProfileProof`). The v2 joint verifier is
analysed with one shared budget over the common query set,
`LfzkV2.Current.ParameterBounds.parentBudget`:

```text
parentBudget = rankError(q_bin) + rankError(q_prime)
             + (1/q_bin + 1/q_prime) * (1 + (L - 1) * tail(a - 1))
rankError(q) = choose(n, k+2s+1) / q^(s+1)        ; batching polynomials B_i
tail(c)      = choose(c, t) / choose(n, t)        ; t queries inside c fixed columns
```

The `1/q` terms are the alpha batching of the equations. For the mdoc
certificate (`LfzkV2.Current.FixedRate.Rate7.certificate`), `a = 867` and
`L = 1272737905242889781956743699885451`, so the column term is
`choose(866, 84)/choose(2443, 84)`. Polygero is charged `c/q` per opaque
query with `c = q * parentBudget`, `1.00000123121490824416 < c <
1.00000123121490824417` (`LfzkV2.Current.Soundness.Rate7.polygeroConstant`).
The Merkle and transcript hash events add to the common correction
`(choose(Q, 2) + r + 15)/2^256`; Polygero contributes two boundaries to `r`
(batching and queries). The full bound and its proof map are in
`formal/README.md`.

**Zero knowledge.** The verifier sees H, Z and `t` columns. Each data row
has `t` uniform prefix samples, so its `t` opened values are uniform
(`LfzkV2.PolygeroCoreMasking`). `f*` is uniform of degree `< k+s` and masks
H (`LfzkV2.PolygeroPrimaryMasking`). `V*u + z_R*m` masks Z without changing
its prefix or its sum over the witness slots (`LfzkV2.PolygeroMasking`).
`LfzkV2.PolygeroZk` combines them into an exact coupling of the backend
transcript. The only statistical loss is Merkle hiding of the unopened
columns, `(Q_pre + Q_post)/2^256`
(`LfzkV2.Current.ZeroKnowledge.StrandCanonicalCommitmentHiding.commitment_hiding`),
which gives the end-to-end `Mdoc.ZeroKnowledge.statClose`.

## Open questions

None.
