# Witness selection design

Witness selection pins the committed witness of every field before any
frontend challenge. Each field commits its frontend cells `w` together with
two dedicated mask cells `m1, m2`. After the joint commitment the verifier
draws two independent uniform coefficient vectors per field, and the prover
answers with two masked linear fingerprints `tj = mj + <aj, w>`. The
fingerprint equations join that field's affine statement for joint Polygero,
which authenticates them at the end of the proof. Outside a collision event of
probability `choose(L, 2)/q^2` per field and query, the responses identify one
candidate in the commitment's list. Every later frontend is then analyzed for
one fixed witness, with no list multiplier.

The protocol is generic over a typed list of fields: GF(2^128) and P-256 in
mdoc, one field in standalone ZK proofs. It sits directly above joint Polygero
(`runtime::v2::polygero`), whose commitment it sends and whose final check it
completes. It is called by the joint wrapper `runtime::v2::zk::joint`
(`JointParam::commit` and `JointParam::receive`), which serves
`runtime::v2::zk` for standalone proofs and `runtime::v2::foreign::compose`
for mdoc. The frontends (sumcheck, split, adapter, dual packing) run between
its two halves on the same transcript and hand it their affine statements.

## Statement

The protocol starts from a joint Polygero commitment and the statement of the
transcript (transcript I1, I3).

| Item | Kind | Source |
|---|---|---|
| Field list `F_1, ..., F_r` | participant order: binary, then prime | statement, one `CommitmentLayout` per field |
| `n_i`, frontend cells of field `i` | derived count | `CommitmentLayout` values (below) |
| Mask cells per field | `FINGERPRINTS = 2` | `CommitmentLayout` "fingerprint mask cells" value |
| Committed vector `z_i = (w_i, m_i1, m_i2)` | `F_i^(n_i + 2)`, private | Polygero witness of field `i` |
| Root | 32 bytes, public | `Commitment` message |

The frontend cells `w_i` are every cell the frontend's statement may read, in
the frontend's order. `n_i` is a function of the `CommitmentLayout` values:
the committed private inputs `p` (private values before packing; for mixed
storage only the native ones), the pad cells, and the packing degree `d`
carried by the packing descriptor:

| Participant | `n_i` |
|---|---|
| Packed circuit, packing degree `d = 1` | `p + pad cells` |
| Packed circuit, packing degree `d > 1` | `ceil(p / d) + pad cells + (d + 1)` packing masks |
| Mixed storage (mdoc prime) | `p + pad cells + 1` (the split mask R) |

These are the counts `PackingLayout::witness_count` and `MixedSplit::new`
produce (`runtime/v2/zk/split.rs`, `runtime/v2/zk/packing_commitment.rs`). The Polygero witness width is
`nw_i = n_i + FINGERPRINTS` (`witness_count` in `fields.rs`), and the masks
are its last two cells, at indices `n_i` and `n_i + 1`.

The protocol ends with, per field, two public coefficient vectors
`a_i1, a_i2 in F_i^(n_i)` (derived from the transcript, never sent) and two
public responses `t_i1, t_i2 in F_i`. Its closing claim is the augmented joint
Polygero statement: for every field, the frontend's equations `A_i w_i + b_i
= 0` and

```text
<a_i1, w_i> + m_i1 - t_i1 = 0
<a_i2, w_i> + m_i2 - t_i2 = 0
```

hold for the committed rows. Joint Polygero proves or checks exactly this
system, with batching weights that the joint opening draws itself after the
last frontend message: one weight per equation of the augmented system,
`e_i + 2` for a field whose frontend statement has `e_i` equations.

## Invariants

**I1. Each field commits `[w | m1 | m2]`, and frontends address only `w`.**
The two mask cells are the last two Polygero witness cells of their field.
Every frontend term addresses an equation of its own statement and a cell
below `n_i`; a term on a mask cell, or on an equation the frontend did not
create, is rejected in both roles before any fingerprint row is appended.
The masks never become circuit inputs.
*Enforced by:* `Field::new` takes `n = nw - FINGERPRINTS` from the augmented
Polygero parameter (`witness_count`) and rejects `nw < FINGERPRINTS`;
`Fields::authenticate` rejects `term.w >= n` and `term.c >= b.len()`
(runtime, shared by both roles); test
`frontend_cannot_address_fingerprint_masks_and_bad_lengths_do_not_consume_masks`.

**I2. The layout is the statement's.** Field identity, `n_i` and the mask
count are those of the statement's `CommitmentLayout` messages: the zk layer
writes each message from the same `CircuitParticipant` whose Polygero
parameter builds the `Field`, and witness selection reads its `Param`
through `Bound<'_, Param<L>>` (transcript I2). Witness selection absorbs no
layout, identity, context or label of its own (transcript I3).
*Enforced by:* no witness selection function takes a layout, field identity
or circuit parameter, and `Field::new(param, domain)` takes no identity
(type); the statement is encoded from the
participant the field is built from (zk I1).

**I3. Coefficients follow the commitment and nothing else.** The `Commitment`
message closes the node (transcript I7). The coefficient vectors are the
first draws from it: for each field in participant order, `a_i1` then
`a_i2`, each `elements(F_i, n_i)`. Every coordinate is an independent uniform
draw; no vector is a power sequence, and no vector is shared between fields
or between `j = 1, 2`.
*Enforced by:* `commit` and `receive` are the only callers of the draw, and
they draw right after the commitment is sent (type: no other entry point);
test `coefficients_follow_the_commitment_and_read_one_stream` checks the
stream segmentation; the role-trace test (transcript I9).

**I4. All responses are sent before any frontend challenge.** `commit` and
`receive` send one `FingerprintResponse` per field, in participant order,
before they return. They draw nothing after the responses. The next draw is
the next sub-protocol's: in mdoc the prime top weights, which the prime
sumcheck draws in P-256 on entry (transcript I8). That draw closes the node that holds both
responses.
*Enforced by:* the frontends need the transcript, which `commit` and
`receive` hold mutably until they have sent every response (type); the
role-trace test and `check_mdoc_round_shapes` (transcript I9); test
`fingerprint_responses_are_bound_before_later_challenges`.

**I5. Completion always appends the fingerprint equations.** The joint
Polygero prover and verifier handles are private fields of the witness
selection states, with the coefficients and responses of the commitment. The
only way to reach `JointPolygeroProver::prove` or
`JointPolygeroVerifier::reduce` is the crate-private `Prover::finish` or
`Verifier::finish`, which the zk layer's `JointProver::finish` and
`JointVerifier::finish` call with the frontend equations of every field. Both
first reject equations derived on another session (each statement's stamp,
compared by address), then append each field's fingerprint rows after its
frontend equations (`Fields::authenticate`), and only then hand the
augmented system to the backend, which draws the batching weights for its
`e_i + FINGERPRINTS` equations per field and uses them in the same call
(Polygero I3). No caller can skip the rows or batch a system without them.
*Enforced by:* private fields and move-only states, and the completion that
appends the rows is the only path to the backend (type); the stamp check
(runtime, both roles; test
`finish_rejects_equations_derived_on_another_session`); `Authenticated` is
constructible only by `Verifier::finish` (type); test
`joint_roundtrip_and_each_forged_response_are_checked_by_backend`.

**I6. One equation form, shared by both roles.** For field `i` with frontend
statement `(A_i, b_i)` of `e_i` equations, fingerprint `j in {1, 2}` is
equation `c = e_i + j - 1`, with terms `(c, k, a_ij[k])` for `k in 0..n_i`,
the mask term `(c, n_i + j - 1, 1)`, and constant `-t_ij`. Frontend equations
keep their indices. The construction is characteristic-free.
*Enforced by:* the single `Fields::authenticate` in `witness_selection.rs`,
called by both roles; test
`both_characteristics_cover_every_cell_and_have_dedicated_masks`; Lean
`LfzkV2.Current.FingerprintRows.rows_iff` and `decoded_view`.

**I7. Masks are fresh, private and used once.** The prover draws each mask
uniformly from its private randomness after the witness lengths are checked,
and each mask occurs in exactly one equation: its own fingerprint row, with
coefficient 1.
*Enforced by:* `ProverFields::append_masks` after `validate_witnesses`
(runtime); I1 and I6 (no other term reaches `n_i` or `n_i + 1`); the masking
lemma `WitnessSelection.maskTranslation` (Lean).

**I8. A state finishes once, on its own transcript.** `Prover` and
`Verifier` are not `Clone`; their `finish` consumes them, with
their coefficients and responses. Each state records the session stamp when
`commit` or `receive` creates it and checks it on the completion call, so it
cannot be completed on another transcript (transcript I2). The joint Polygero
state inside it does the same.
*Enforced by:* move-only (type); the session stamp check (runtime; test
`prover_and_verifier_states_complete_only_on_their_own_session`).

## Protocol

`r` fields in participant order; `n_i` and `F_i` as in the Statement. Tags
are from the transcript registry.

| Step | Sender | Message or draw | Values | Size |
|---|---|---|---|---|
| 1 | prover, via joint Polygero (the opening message) | `Commitment` (32) | Bytes(32) root | 32 bytes |
| | | node ends: ROUND | | |
| 2 | draw | for `i = 1..r`: `a_i1`, then `a_i2` | `elements(F_i, n_i)` each | `2 n_i` elements per field |
| 3 | prover | `FingerprintResponse` (33), for `i = 1..r` | Elements(`F_i`, 2): `t_i1`, `t_i2` | 2 elements per field |
| | | node ends: ROUND, at the caller's next draw | | |

In mdoc `r = 2` (GF(2^128) host, then P-256 split participant), so the
first draw row of the transcript schedule reads `2 x Elements(GF2_128, n_1),
2 x Elements(P256, n_2)`, and the node holding both responses closes with the
prime top weights. In a standalone ZK proof `r = 1`, and the node closes at
the caller's next draw, the circuit's top weights. For a circuit with zero
layers they are its input-assertion weights: that draw still closes the
node, and the zero-layer sumcheck then sends nothing. Later draws before the
next message continue the same stream (transcript I7).

Completion runs after every frontend message:

| Step | Sender | Message or draw | Values |
|---|---|---|---|
| 4 | both roles | check the equations' session stamps, then append the fingerprint rows (I5, I6); no message | |
| 5 | joint Polygero | batching weights, drawn and used inside `prove`/`reduce` | per field: `e_i + 2` weights, then `s + 1` samples per batched row |
| 6 | prover | `PolygeroResponse` (96), one per field, sent by joint Polygero | Elements(`F_i`, k+s), Elements(`F_i`, 2k) |

Witness selection sends and draws nothing in steps 4 to 6 itself; it appends
the rows to the frontend equations and hands the augmented system to joint
Polygero, which draws its batching weights at the boundary after the last
frontend message and begins by sending `PolygeroResponse`. Appending the rows
writes nothing to the transcript, so the draw position is the one the
frontends leave.

The prover's responses are `t_ij = m_ij + <a_ij, w_i>` (`ProverFields::responses`,
one `blas::dot` of length `n_i` per response). Its cost is `2 n_i`
multiplications and `2 n_i` coefficient samples per field.

Verifier checks:

| When | Check | Where |
|---|---|---|
| Proof parse | exactly 2 canonical elements of `F_i` per field | `FingerprintResponse::read` |
| After the frontends | each field's equations carry this session's stamp; each frontend term has `w < n_i` and `c < e_i` | `Fields::authenticate` |
| After the frontends | the augmented system holds for the committed rows | `JointPolygeroVerifier::reduce` |

The early responses are not checked arithmetically. They fix the targets;
only the final Polygero check authenticates them. `Authenticated` is
intermediate evidence; complete verification also needs the seal
(transcript I10).

## Formats

### Transcript messages

Every integer is u64 little endian; elements use canonical serialization
(transcript I5).

```text
commitment  := u64(32) u64(0) u64(32) root[32]                  ; 56 bytes
response(F) := u64(33) u64(2) u64(FieldID(F)) u64(2) t1 t2      ; 32 + 2*size(F) bytes
selection   := commitment ROUND response(F_1) ... response(F_r)
```

| Field | FieldID | `size(F)` | `response` bytes |
|---|---|---|---|
| GF(2^128) | 4 (`Gf2_128`) | 16 | 64 |
| P-256 | 1 (`P256`) | 32 | 96 |

The coefficient draws consume the node's stream as the transcript's
`elements(F, n)` kind: 16 bytes per GF(2^128) coordinate; for P-256, the
sample byte count with the top byte masked and rejection at or above the
modulus. Witness selection writes no other transcript bytes.

### Proof body

The response block follows the 32-byte commitment root in the proof body, in
participant order, with no length prefixes or tags; its length is fixed by
the absorbed field list (transcript I11).

```text
responses := t_11 t_12 ... t_r1 t_r2        ; canonical elements of F_i
```

| Proof | Layout | Bytes |
|---|---|---|
| mdoc (`ComposedProof::fingerprints`) | GF(2^128) `t_11 t_12`, then P-256 `t_21 t_22` | 32 + 64 = 96 |
| standalone ZK (`ZkProof::fingerprints`) | `t_11 t_12` in the circuit's field | `2 size(F)` |

Masks and coefficients are never serialized. The responses are interactive
proof fields (transcript I4): absorbed once as `FingerprintResponse`, and
again only inside the seal.

## Rust API

```rust
// runtime::v2::proto::witness_selection
pub const FINGERPRINTS: usize = 2;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FingerprintResponse<E> { pub values: [E; FINGERPRINTS] } // exactly two (I6)
impl<E> FingerprintResponse<E> {
    pub fn write<F: SerializableField<E = E>>(&self, out: &mut Vec<u8>, f: &F);
    pub(crate) fn read<F: SerializableField<E = E>>(input: &mut &[u8], f: &F)
        -> io::Result<Self>;           // only the complete readers call it (proto I2)
}

// runtime::v2::witness_selection, crate-private: the zk joint wrapper drives it
pub(in crate::runtime::v2) fn witness_count(cells: usize) -> Result<usize, String>; // n + 2
/// Message tag 33: one Elements(F, 2) value, in transcript.rs. Holds a reference to its field.
struct ResponseMessage<'a, F: RegisteredField> { f: &'a F, response: &'a FingerprintResponse<F::E> }

/// One field of the list, built from its augmented Polygero parameter; n = nw - 2 (I1, I2).
pub(crate) struct Field<'a, F, D> { backend: Participant<'a, F, D>, f: &'a F, cells: usize }
impl Field<'a, F, D> {
    pub(crate) fn new(param: PolygeroParam, domain: &'a D) -> Result<Self, String>;
}

/// Typed list (Field, Tail) ending in (); sealed. Keeps each field's element type.
pub(crate) trait Fields: Sealed + Clone {
    type Backend: Participants + Clone;
    type Coefficients;                 // ([Vec<F::E>; 2], Tail::Coefficients), derived, not serialized
    type Responses: Clone;             // (FingerprintResponse<F::E>, Tail::Responses)
    fn backend(&self) -> Self::Backend;
    fn coefficients(&self, r: &mut Reading<'_>) -> Self::Coefficients;                 // I3
    fn send_responses(&self, responses: &Self::Responses, t: &mut TranscriptRef<'_>);  // I4
    // called only by Prover::finish and Verifier::finish
    fn authenticate(&self, statements: Statements<Self>, coefficients: Self::Coefficients,
                    responses: &Self::Responses, session: &SessionStamp)
        -> Result<Statements<Self>, String>;                                         // I1, I5, I6
}
pub(crate) type Statements<L> = <<L as Fields>::Backend as Participants>::Statements;
pub(crate) type Bodies<L>     = <<L as Fields>::Backend as Participants>::Bodies;

/// Statement part: the field list and the joint Polygero parameter.
pub(crate) struct Param<L: Fields> { fields: L, backend: JointPolygeroParam<L::Backend> }
impl<L: Fields> Param<L> {
    pub(crate) fn new(fields: L) -> Result<Self, String>;  // only zk's JointParam::new builds one
    pub(crate) fn config(&self) -> PolygeroConfig;
}

// prover role
pub(crate) type Witnesses<L>  = <<L as Fields>::Backend as Participants>::Witnesses;
pub(crate) trait ProverFields: Fields<Backend: ProverParticipants> { /* validate_witnesses, append_masks, responses */ }
pub(crate) struct Prover<S, C, R> { backend: JointPolygeroProver<S>, session: SessionStamp,
                                    coefficients: C, responses: R }
// JointParam::commit only
pub(crate) fn commit<L: ProverFields>(
    t: &mut Bound<'_, Param<L>>, witnesses: Witnesses<L>, rng: &mut impl PrivateRandom,
) -> Result<(Prover<..>, PolygeroCommitment, L::Responses), String>;  // sends Commitment, draws, sends responses
impl<S, C, R> Prover<S, C, R> {
    // JointProver::finish only: stamps, fingerprint rows, then the backend's prove
    pub(crate) fn finish<L: Fields<Coefficients = C, Responses = R>>(
        self, t: &mut Bound<'_, Param<L>>, statements: Statements<L>,
    ) -> Result<JointPolygeroProof<Bodies<L>>, String>;            // I5, I8
}

// verifier role
pub(crate) trait VerifierFields: Fields<Backend: VerifierParticipants> {}
pub(crate) struct Verifier<L: Fields> { backend: JointPolygeroVerifier<L::Backend>, session: SessionStamp,
                                        coefficients: L::Coefficients, responses: L::Responses }
impl<L: VerifierFields> Verifier<L> {
    // JointParam::receive only
    pub(crate) fn receive(t: &mut Bound<'_, Param<L>>, root: &PolygeroCommitment,
                   responses: L::Responses) -> Self;                 // same schedule as commit (I3, I4)
    // JointVerifier::finish only: stamps, fingerprint rows, then the backend's reduce
    pub(crate) fn finish(self, t: &mut Bound<'_, Param<L>>, statements: Statements<L>,
                         proof: &JointPolygeroProof<Bodies<L>>)
        -> Result<Authenticated, String>;                                // I5, I8
}
pub(crate) struct Authenticated { .. } // only from finish; not a VerifiedProof
```

How the API carries the invariants:

- Nothing takes a layout, field identity, root context or label: the field
  list is a statement part, read through `Bound` (I2).
- `commit` and `receive` run the whole early exchange in one call. The caller
  gets the transcript back only after the responses are sent, so a frontend
  challenge cannot precede them (I4).
- The coefficient vectors are drawn with `Field::cells` coordinates each, so
  their lengths equal `n_i` by construction (I3).
- The backend handles, coefficients and responses are private fields of
  move-only states. The only completions append the fingerprint rows (I5, I8).
- `Fields` is sealed and implemented only for `()` and `(Field, Tail)`, so
  one, two or more fields run the same code, in participant order.

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| A frontend equation reads or writes a mask cell | I1: `authenticate` rejects `w >= n` in both roles |
| A frontend term names an equation it did not create | I1: `authenticate` rejects `c >= b.len()` |
| Fingerprinting only the private inputs, not pads, packing masks or R | Statement: `n_i` is every frontend cell (Lean `FingerprintRows.rows_realized`) |
| Completing Polygero without the fingerprint rows | I5: the backend handle is private |
| Batching weights sized for the frontend equations only | I5: the rows are appended before the backend draws its weights, for the augmented counts |
| Equations derived on another session reaching the opening | I5: `authenticate` compares each statement's session stamp with the state's |
| Drawing coefficients before the commitment is fixed | I3: the draws follow the `Commitment` message in `commit`/`receive` |
| Drawing a frontend challenge before the responses are sent | I4: the transcript is held by `commit`/`receive` until every response is sent; transcript I8 |
| Choosing a response after a frontend challenge | I4: responses are in the node closed by the first frontend draw |
| Power-sequence or shared coefficient vectors | I3: independent `elements(F, n)` draws per vector and field |
| Absorbing the layout, root or context a second time | I2: the layout is in the statement; transcript I3 |
| Prover and verifier disagree on a field's identity or width | I2: both build the field from the participant that writes the `CommitmentLayout` |
| A response with one coordinate, or a non-canonical element | `[E; 2]` type; `FingerprintResponse::read` rejects short or non-canonical input |
| Reusing masks or deriving them from public data | I7: masks come from `PrivateRandom` in `append_masks` |
| Running the completion twice, or on another transcript | I8: move-only states and the session stamp check |
| A characteristic-specific sign error in the rows | I6: constant `-t` with `+m` and `+<a, w>` holds in every characteristic |

## Soundness and zero knowledge

**What each check is for.**

| Mechanism | Purpose |
|---|---|
| Commitment before coefficients | Pins each field's candidate list: the list-decoding candidates of the committed rows, projected to `(w_i, m_i)`, independent of `a` |
| Two independent full vectors | A pair of distinct candidates collides with probability at most `1/q^2`; equal `w` with different masks never collides |
| Responses before any frontend challenge | The response pair selects at most one candidate outside the collision event, before the frontends draw, so each frontend pays its fixed-witness bound once |
| Fingerprint rows in the joint statement | Polygero authenticates the responses against the same committed rows the frontends constrain |
| Masks in no other equation | Keeps the response-hiding argument valid; the masks do not enter the collision bound |

**Error terms.** For a field with a commitment-fixed projected list of size
at most `L` over a field of size `q`:

| Term | Value | Lean |
|---|---|---|
| Pair collision | `1/q^2` | `WitnessSelection.pair_collision_card_mul_le` |
| List collision | `choose(L, 2)/q^2` | `WitnessSelection.list_collision_card_mul_le` |
| Unique selection outside the event | no error | `WitnessSelection.unique_matching_candidate`, `select_of_match` |
| Later frontend, fixed witness | the frontend's own bound, no list factor | `WitnessSelection.selected_bad_card_le`; `SumcheckV2.selected_round_bad_card_le` (2 roots per quadratic round) |
| Adaptive Fiat–Shamir, `Q` distinct queries | `Q * choose(L, 2)/q^2 + (Q + 1)/2^256` | `WitnessSelection.Chained.failure_bound` |
| Composition with Polygero | `selectionError + fixedWitnessError` replaces the frontend term | `RecursivePolygero.NonrecursiveFS.selected_frontend_ratio_le` |

Several fields sum their charges, without an independence assumption; the
chain exception `(Q + 1)/2^256` is charged once for the whole proof. In mdoc
the per-query fingerprint charge is
`choose(LB, 2)/2^256 + choose(LN, 2)/p^2`
(`LfzkV2.Current.ApplicationCharging.roundBudget`, role `.fingerprint`), and
`LfzkV2.Current.CertifiedProfile.fingerprint_budget_le` bounds it by
`2/(2^128 - 1)`. The rate-1/7 profile `(k, s, n, t) = (349, 12, 2443, 84)`
has caps `LB = 21898356682154715916` and `LN = 451457457136012100305`
(`LfzkV2.Current.FixedRate.Rate7`, in `Parameters/Rate7.lean`), so the
binary term is about `2^-128.5` and the prime term about `2^-375.8`. With one
fingerprint per field the binary term would be about `2^-0.5` and the prime
term about `2^-119.8`; both fields need two.

The selected pair is the same at every later query of an accepted path:
`LfzkV2.Current.Selection.atPoint` reconstructs it from the coefficient answer
and the responses bound in the next boundary, and
`LfzkV2.Current.Selection.atPoint_replay` proves the path identity.
`LfzkV2.Current.FingerprintRows.decoded_view` derives both the frontend rows
and the fingerprint match from the backend decoder, so authentication is a
theorem, not a premise. Selection is an analysis object: the Polygero
extractor still replays the frontends to rebuild its statement, and no
extractor running-time bound is claimed.

**Zero knowledge.** For fixed `a` and `w`, the map from masks to responses is
a translation, `WitnessSelection.maskTranslation`, so uniform private masks
make the responses uniform and independent of `w`. The fingerprint rows are
ordinary equations of the joint statement, so Polygero's hiding covers its
`H`/`Z` responses for them like any other row. The complete-view theorem
`LfzkV2.Current.Mdoc.ZeroKnowledge.statClose` includes the early responses
and bounds the real/simulated distance by `(Qpre + Qpost)/2^256`. The
argument needs I7: a mask that occurs in a second equation need not
hide its response.

**Lean modules.** `formal/witness-selection` (`WitnessSelection.Algebra`,
`Collision`, `ChainedFiatShamir`, `APITest`);
`formal/sumcheck-v2/SumcheckV2/WitnessSelection.lean`;
`formal/polygero/FiatShamir/WitnessSelection.lean`; and in
`formal/lfzk-v2/LfzkV2/Current`: `FingerprintRows`, `TaggedFormat` (the
first-node bytes), `Selection`, `SelectionReplay`, `SelectionPath`,
`ApplicationCharging`, `CertifiedProfile`.
