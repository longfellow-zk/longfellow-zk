# v2 ZK frontend design

`runtime::v2::zk` turns layered circuits into authenticated affine claims. A
field participant commits one cell vector per field; its circuits run as one
layered sumcheck; the constraint compiler lowers the sumcheck constraints to
rows `A*w + b = 0` over the committed cells; packing, the split or row
batching reduce the input equation; and the joint wrapper authenticates every
participant's rows together. It works in any `ZkField` with a `PackingField`
view: GF(2^128) with degree-128 bit packing for the hash host, and P-256 with
degree-one packing, possibly with foreign storage, for the signature circuit.
Below it sit sumcheck (which supplies `Constraints`) and dual packing. Above
it, witness selection and joint Polygero consume its `LinearStatement`s, and
the foreign adapter consumes its `ModularClaim`s. Its transcript obligations
are those of the [transcript design](../transcript/DESIGN.md); this document
cites them as "transcript I1" and so on.

## Statement

**Input.** The statement part of one field participant, absorbed once in the
transcript statement (transcript I1, I3) and read through `Bound` (transcript
I2):

| Item | Value | Statement message |
|---|---|---|
| Circuits | `circuits[0]` (primary), then the others, in order | one `Circuit` each: its ID, which binds its layer widths, output count, `ninput` and `npublic_input` |
| Input layout | public, committed private, virtual (in that order), width `max ninput` | derived from `Circuit` and `CommitmentLayout` |
| Commitment layout | field, committed private inputs (before packing), pad cells, fingerprint cells, packing descriptor (which carries the packing degree `d`), native and bit-stored storage runs, mask group | one `CommitmentLayout` |
| Public inputs | `x_pub` in `F^npublic`, as the circuit sees them | `PublicInputs` |

The prover knows private inputs `x_priv` (bits for binary circuits, field
elements for prime circuits) such that every circuit's outputs and assertions
vanish on the shared input array `[x_pub | x_priv | v]`. The virtual suffix
`v` has one entry `c0 + c1 * x[source]` per virtual input, with `source` in
the committed range.

**Output.** After the frontend's messages, each participant holds:

| Storage (participant type) | Output | Consumer |
|---|---|---|
| native (`CircuitParticipant`, any `d`) | `LinearStatement`: rows `sum_w A[c,w]*w + b[c] = 0` over its committed cells | joint Polygero, with witness selection's two fingerprint rows appended |
| mixed (`split::MixedSplit`) | `LinearStatement` (layer rows and one native row) and one `ModularClaim` | joint Polygero; foreign adapter |
| pure foreign (`split::pure::PureSplit`, tests only) | one `ModularClaim` with a public target | foreign adapter |

A `ModularClaim` is `sum_i k_i * val(G_i) = target (mod p)`, where each `G_i`
is a bit group of the binary input array and `val` reads it least
significant bit first. All outputs together hold for the committed values if
and only if every circuit is satisfied, except with the error terms in
[Soundness and zero knowledge](#soundness-and-zero-knowledge).

## Invariants

**I1. One committed cell vector per field, with a layout fixed by the
statement.** Each participant commits exactly one vector, in this order:

| Storage | Committed cells |
|---|---|
| native | packed words, pads, packing masks, fingerprint masks |
| mixed | native private inputs, pads, R, fingerprint masks |
| pure foreign | none |

Packed words are `ceil(committed/d)`. Pads are
`sum over layers of (2*logw + 4)`, with `logw` the layer's round count in
the participant's combined sumcheck geometry. Packing masks are `d+1` for `d > 1` and
none for `d = 1`. Fingerprint masks are `FINGERPRINTS = 2`, appended by
witness selection after every frontend cell. Every position is a function of
the `Circuit` and `CommitmentLayout` messages, and both roles derive it from
the same object that wrote those messages.
*Enforced by:* `PackingLayout::new` and `MixedStorage::new` are the only
constructors (private fields), and each storage mode is its own
participant type, with only the fields its cells need (type); `witness_selection::witness_count`; the
statement is encoded from the participant object the frontend reads
(transcript I2). Lean `CellLayout.selected` covers only the last step: witness
selection appends its two masks after every frontend cell
(`Fin cells ⊕ Fin 2 ≃ Fin (cells+2)`); the rest of the layout is checked in
Rust.

**I2. The frontend absorbs only its own prover messages.** Circuit IDs, layer
widths, input counts, the commitment layout, the storage runs, the mask group
and the public inputs are in the statement. After it, the zk layer sends only
`SplitOpening`, and sumcheck and dual packing send theirs. Nothing derived is
absorbed: input weights, claim targets, eta-scaled weights, row-batching
weights, virtual input definitions and the rows of a `LinearStatement` are
recomputed by both roles. A `LinearStatement` carries no digest.
*Enforced by:* zk functions reach the transcript only through `Bound`,
whose only write is `TranscriptRef::send` of a `ProverMessage`; setup
messages are `SetupMessage`s, which only the statement writes (type); the
role-trace test (transcript I9).

**I3. Frontends read circuits, layout and public inputs from `Bound`.**
`prove`, `reduce`, `prove_split` and `reduce_split` take a
`Bound<'_, FrontendPart>` and no circuit, public-input or geometry parameter.
`FrontendPart::new` checks once, before the transcript exists, that the
circuits are the participant's circuits in order, that the public count is
the primary circuit's `npublic_input`, and that the input layout matches. The
proof reader parses `CircuitProof` against the geometry the statement
writes, which comes from the same participant (`Opened::geometry`).
*Enforced by:* function signatures (type); `FrontendPart::new` (runtime,
before `Opened::new`).

**I4. Every step draws its own leading challenge.** The sumcheck top
weights are drawn by the sumcheck that `prove`, `prove_split`, `reduce` and
`reduce_split` run, on entry, from the boundary closed by the previous
message (transcript I8); eta is drawn by `PendingSplit::open` and
`SplitClaim::receive` on entry, right after the frontend's last answer. A
frontend's virtual-input definitions are an argument of the call that draws
its top weights, so they are fixed before them. The pure-foreign row weights
are drawn by the pure split step itself (`PureClaim::batch`), at the
frontend's last boundary, and used in the same call. The Polygero batching
weights are drawn and consumed by the opening itself: `JointProver::finish`
and `JointVerifier::finish` take each field's frontend equations
(`Statements<L>`, typed per field, in participant order) after the last
frontend message of every participant (`PackingA`, or the last
`SumcheckClaims` when every participant has degree one), consume the
session, reject equations derived on another session (the stamp each
`LinearStatement` carries), attach the fingerprint equations and run joint
Polygero, which draws the weights at that boundary and uses them in the same
call. No caller holds a challenge, so none can pair one with another system.
Eta has the private type `Eta<E>`, whose only constructor is its
`nonzero(F)` draw (`split::transcript::eta`), so a zero eta cannot be
represented.
*Enforced by:* the draws are inside these entry points, none of which takes
a challenge as a parameter; `Eta` is private to the split and built only by
its draw; `LinearStatement` has no public constructor outside tests and
tools, and `finish` takes every field's equations in their types (type; a
`compile_fail` doctest on `LinearStatement`); the stamp check (runtime; test
`finish_rejects_equations_derived_on_another_session`).

**I5. One constraint form, compiled by shared code.** Every row is
`sum_w A[c,w]*w + b[c] = 0`. Coefficients, constants, explicit zeros and
repeated terms are kept. Public inputs and virtual inputs are substituted:
their weighted constants move into `b`, and each virtual coefficient joins
its source input's weight. Logical pads `(layer, round, slot)` map to
committed cells through `CircuitPadLayout`. Both roles call
`compile_layers` and `compile_packed` on the `Constraints` that sumcheck
returns; a split participant's rows over its values come from one lowering,
`batching::rows` (the layer rows from `compile_layers`, the input target
from the compiler's `input_target`, as in `compile_packed`), which mixed
storage then maps from value indices to its native cells
(`MixedSplit::split_claim`).
*Enforced by:* the compiler lives in shared code used by both role modules;
tests `symbolic_and_compiled_constraints_match_numerical_binary` and
`_prime`; Lean `LfzkV2.Compiler.compile_correct`.

**I6. The witness is selected before any frontend challenge.** The joint
handle takes the `Transcript` by value at commit or receive, sends the
`Commitment` root, draws the fingerprint coefficients and sends every field's
`FingerprintResponse` before it returns. Frontends get their `Bound` only
from that handle.
*Enforced by:* ownership: `JointProver` and `JointVerifier` own the
transcript, and a frontend reaches it only through their crate-private
`bound()`, which binds it to the frontend's statement part; they have no
public transcript accessor (type); Lean `ZkJoint`, `FingerprintRows`.

**I7. A frontend output is not an acceptance decision.** `LinearStatement`
and `ModularClaim` are `#[must_use]` claims. Acceptance requires
`JointVerifier::finish`, which takes the `Unverified` complete proof,
checks its joint opening and returns an `Authenticated` that keeps the
proof, and then `Authenticated::check_seal`, which checks the seal of that
proof on the authenticated session and alone returns its `VerifiedProof`
(transcript I10).
*Enforced by:* `Authenticated` is obtainable only from `finish`; the
verifier's transcript leaves the joint handle only inside it and never
leaves `Authenticated` outside tests, so the seal can be checked only on an
authenticated session; `check_seal` takes no proof, so it checks the seal
of the proof whose opening `finish` checked (type).

**I8. Virtual inputs are substituted, never committed and never absorbed.**
The primary circuit ends before the virtual suffix and cannot read it. Each
definition's source lies in the committed range. The definitions must be
deterministic functions of the prior protocol (statement values and earlier
messages and challenges), fixed before the caller draws this frontend's top
weights: if they could depend on those weights, the weighted output test
would not test one fixed circuit instance. This provenance is the caller's
obligation: the shape and source checks below do not enforce it, since
`VirtualInputs` are plain data (open question 1). The foreign drivers
compute the leaves before they draw the host top weights.
*Enforced by:* `InputLayout::new` and `VirtualInputs::validate` (runtime);
`compile_packed`; test `binary_virtual_inputs_are_substituted_not_committed`;
Lean `LfzkV2.InputBinding` (virtual inputs).

**I9. Mixed storage splits only the input equation, with one eta and one
mu.** Every pad is native, so the layer rows read only native cells and go
to Polygero unbatched. The input equation `<w, v> = t` is split by one
nonzero `eta` and one message `mu = eta*<w_F, v_F> + R` into the native row
and the modular claim, both produced by the one call that sends or receives
`mu`. R is uniform in `F` and committed as a native cell and as bits in the
binary commitment. The split puts it in two equations, the native row and
the modular claim; like every committed cell, its cell and its bits also
enter their fields' fingerprint equations (witness selection I5).
*Enforced by:* `MixedStorage::new` (pads native, some value native, R's
bits given); `MixedSplit` is the only participant type with a mask, and
`prove_split`, `reduce_split`, `open` and `receive` take only its parts
(type); `PendingSplit::open` and `SplitClaim::receive` consume the claim and
return both outputs (type); Lean `Prime.Claim.rows`, `Handoff.split_handoff`.

**I10. Storage maps are canonical.** Each value has exactly one storage.
Native cells are numbered densely in value order. `runs()` returns maximal
runs, so equal maps give equal runs and the statement's run encoding is
injective.
*Enforced by:* `StorageMap::new` (runtime); `Group` fields are private and
its end cannot overflow (type); test
`storage_runs_are_maximal_and_canonical`.

**I11. Row batching exists only for pure foreign storage, and covers every
row.** A pure-foreign participant commits nothing, so independent weights
`rho_0..rho_L` batch its `L` layer rows and its input equation into one
modular claim with a public target. Mixed and native storage never batch.
A pure-foreign participant writes a `CommitmentLayout` with zero cells and
zero fingerprint cells, and it is not a joint field: it has no Polygero
parameter, no fingerprint masks and no rows, and its `CircuitProofGeometry` has
`nw = 0`. Lean models row batching (`RowBatching`, `PureHandoff`,
`PureComposition`), but no application may use pure-foreign storage until
its application model charges those events. The composition driver
(`foreign::compose::Composition`) supports mixed storage only; a
pure-foreign composition is future work, and the pure path is compiled for
tests only.
*Enforced by:* pure-foreign storage is its own participant type,
`PureSplit`, whose map `StorageMap::check_pure` checks and which has no
Polygero parameter and no `participant()`, so it cannot join a
`JointParam`; `PureClaim::batch`, the only step that draws and uses row
weights, takes only a `PureSplit`'s part (type; test
`pure_foreign_participant_cannot_join_the_joint_backend`); Lean
`ApplicationCharging` (no row batching in the mdoc schedule).

**I12. One Polygero profile per proof.** Every participant of a proof uses
the one `PolygeroConfig` of the statement's `JointGeometry`, so all fields
share `(k, s, n, t)`, one tuple-column Merkle tree and one query set.
A composition gives every participant its one profile (`Composition::new`
takes one config), and `JointGeometry` writes the config of the proof
geometry, which is the joint parameter's.
*Enforced by:* `ZkProofGeometry` and `ComposedGeometry` hold one config
(type); `JointPolygeroParam::new` rejects participants whose profiles differ
(runtime).

## Protocol

The zk layer's part of one proof, in transcript order. `L` is the number of
layers of the participant's combined sumcheck, `d` the packing degree,
`cells` the participant's frontend cell count (without fingerprint masks).
Sumcheck, packing and Polygero messages are owned by those protocols and
listed for position only.

| Step | Sender | Message or draw | Values |
|---|---|---|---|
| Statement | both | `Circuit` x m, `CommitmentLayout`, `PublicInputs` per participant; one `JointGeometry` | see Statement |
| Commit | prover | `Commitment` | Bytes(32) root |
| | draw | fingerprint coefficients, per field | 2 x Elements(F, cells) |
| | prover | `FingerprintResponse`, per field | Elements(F, 2) |
| Frontend | draw | top weights (*leading*, drawn by the sumcheck) | sumcheck |
| | prover | `SumcheckRound` x logw, `SumcheckCross`, `SumcheckClaims`, per layer | sumcheck |
| Packing, `d > 1` | prover | `PackingU` | Elements(F, d) in the participant's field |
| | draw | packing challenges | d independent elements(F) |
| | prover | `PackingA` | Elements(F, 1) |
| Split, mixed | draw | eta (*leading*, drawn by `open` and `receive`), after the last stage's alpha and input assertions | nonzero(F) |
| | prover | `SplitOpening` | Elements(F, 1): mu |
| Batching, pure | draw | rho, drawn and used by `PureClaim::batch`, after the last stage's alpha and input assertions | elements(F, L+1) |
| Authenticate | draw | Polygero batching weights, drawn and used inside `finish`, after the last frontend message | joint Polygero |
| | prover, draw | `PolygeroResponse` per field, then t column indices | joint Polygero |

`d = 1` packing has no messages and no boundary: it yields one direct row.
A frontend whose circuits all have zero layers still draws its top weights,
which are its input assertions (transcript I8); its sumcheck then sends and
draws nothing. With `d > 1` its packing still sends `PackingU`, draws the
packing challenges and sends `PackingA`. With `d = 1` the frontend sends
nothing, and the next draw (eta or rho for a split participant) reads
further from the boundary closed by the previous message. Every frontend of
every participant finishes before the caller calls `finish`, which draws the
Polygero batching weights. In mdoc the order is: commit, prime frontend, eta,
`SplitOpening`,
the adapter's conversion pair and `P256AdapterQuotients`, the host frontend
over the hash circuit and the adapter fragment, `PackingU`, `PackingA`, then
joint Polygero. For pure foreign storage, `PureClaim::batch` draws rho at
the frontend's last boundary, before the adapter's conversion pair, from the
same stream;
no composition runs this schedule (I11).

### Reductions

Both roles run the same arithmetic after the frontend's messages.

1. **Compile.** Sumcheck returns `Constraints { layers, input_claim,
   input_weights }`. Each layer gives one row: its `PadExpression` with pads
   mapped to cells. The input equation is
   `input_claim.constant + sum k*pad - <input_weights, inputs> = 0`.
2. **Substitute.** `t = input_claim.constant - <w_pub, x_pub> - sum_j
   w_virt[j]*c0[j]`, and `w[source_j] += w_virt[j]*c1[j]`. The private
   weights then cover only committed inputs.
3. **Native, any `d`.** `compile_packed` emits the layer rows and the source
   claim `<w_priv, x_priv> = t + sum k*pad` for dual packing. Packing returns
   one row (`d = 1`) or two rows (`d > 1`) over packed words, pads and
   packing masks, appended after the layer rows.
4. **Mixed.** Over the value vector `v = [private | pads]`, the weights are
   `w[i] = w_priv[i]` for inputs and `w[j] = -k` for pad `j`, so the input
   equation is `<w, v> = t` (`batching::rows`, as for pure foreign storage;
   the layer rows then move from value `i` to its native cell). With `F` the foreign and `N` the native values:

   ```text
   mu = eta*<w_F, v_F> + R                                  (prover)
   native row:     eta*<w_N, v_N> - R + mu - eta*t = 0      (Polygero)
   modular claim:  <eta*w_F, v_F> + R_bits = mu  (mod p)    (adapter)
   ```

   The native row follows the `L` layer rows, so the statement has `L+1`
   rows. The claim's terms are the foreign groups in value order, then R's
   group with coefficient 1.
5. **Pure foreign.** With layer rows `A_c*v + b_c = 0`:
   `weights = sum_c rho_c*A_c - rho_L*w_priv + rho_L*k_pads`,
   `target = -(sum_c rho_c*b_c + rho_L*t)`, and the claim is
   `<weights, v_F> = target (mod p)` over every value.

### Verifier checks

| Check | Where |
|---|---|
| Circuits, public count and input layout match the participant | `FrontendPart::new`, before the transcript |
| Proof shape: sumcheck layers and rounds, packing `U` length `d` | `CircuitProof::read` against the bound geometry |
| Virtual definitions: count and source range | `VirtualInputs::validate` |
| Constraint shape: layer count, input weight count `committed_end + virtual` | `compile_packed`, `split_claim`, `batch` |
| Packing rows: count 1 or 2, word, mask and pad ranges | `PackingCommitment::append_equations` |
| Eta drawn at the frontend's last boundary | `PendingSplit::open`, `SplitClaim::receive` draw it on entry |
| All rows and claims hold | joint Polygero (`JointVerifier::finish`) and the foreign adapter |

## Formats

All integers u64 little endian; field elements in canonical serialization
(GF(2^128): 16 bytes, P-256: 32 bytes).

### Commitment layout

The zk participant supplies the `CommitmentLayout` message values:

| Value | Native | Mixed | Pure foreign |
|---|---|---|---|
| FieldID | `F::field_id()` | prime `F` | prime `F` |
| committed private inputs, before packing | `InputLayout::committed()` | native private inputs | 0 |
| pad cells | `pad_count()` | `pad_count()` | 0 |
| fingerprint cells | 2 | 2 | 0 |
| packing descriptor | `PackingParameters::descriptor()`, carrying `d` | same, `d = 1` | same, `d = 1` |
| native runs | empty | `Run::Native` of `runs()` | empty |
| bit-stored runs | empty | `Run::Prime` of `runs()` | `Run::Prime` of `runs()` |
| mask | (0, 0) | (R start, R width) | (0, 0) |

The runs are two lists of one fixed arity each, both in increasing first
value: `first, count, cell` triples for `Run::Native` and
`first, count, start, width` quadruples for `Run::Prime`. Mixed and pure maps
are told apart by their runs: a mixed map has a native run, a pure map has
none.

### Proof fields

```text
circuit_proof := sumcheck packing
sumcheck      := layer{L}                      ; owned by sumcheck
layer         := (elem elem){logw} elem elem elem  ; rounds, cross, two claims
packing       := ""                            ; d = 1
               | elem{d} elem                  ; d > 1: U, then A
split_opening := elem                          ; mu, one element of F
```

Sizes, in elements: sumcheck `sum_l (2*logw_l + 3)`, packing `0` or `d+1`,
split opening 1. A `LinearStatement` and a `ModularClaim` are never
serialized.

The standalone proof `ZkProof` is below. Its outermost magic is `LFV9`
(transcript I11); the protocol ID `longfellow/v2/zk/transcript/v2` rejects
proofs of another format at the statement.

```text
zk_proof := "LFV9" root fingerprint circuit_proof polygero seal
root        := byte{32}
fingerprint := elem elem
polygero    := joint Polygero body, without nested magic or context (transcript I11)
seal        := first PRF block of the seal node (transcript I10)
```

Composed proofs place the same `circuit_proof` and `split_opening` fields in
`proto::composed::ComposedProof`, in send order.

## Rust API

```rust
// runtime::v2::zk: setup, shared by both roles
// virtual inputs, crate-private: only the composition driver defines them
pub(crate) struct VirtualInput<E> { pub(crate) source: usize, pub(crate) constant: E, pub(crate) coefficient: E }
pub(crate) struct VirtualInputs<E> { pub(crate) entries: Vec<VirtualInput<E>> }
impl<E> VirtualInputs<E> { pub(crate) fn none() -> Self; }
pub(crate) fn write_joint_geometry(h: &mut Header<'_>, config: PolygeroConfig);  // JointGeometry
pub type CircuitInput<F> = BaseElement<<F as PackingField>::Packing>;

// zk::joint
// what every storage mode shares: circuit IDs, geometry, profile, input layout, packing
pub(crate) struct Frontend<F> { .. }
pub struct CircuitParticipant<F> { .. }   // native: a Frontend and its Polygero parameter
impl CircuitParticipant<F> {
    pub fn new(circuits: &[&Circuit<F>], virtual_inputs: usize,
               config: PolygeroConfig, domain: &D) -> Result<Self, String>; // the proof's one profile (I12)
    pub fn geometry(&self) -> CircuitProofGeometry;           // written as Circuit/CommitmentLayout (I1)
    pub(crate) fn field(&self) -> &F;                    // the domain's field at construction
    pub(crate) fn participant(&'a self, domain: &'a D) -> Result<witness_selection::Field<'a, F, D>, String>;
}
// the statement writes every storage mode alike, from its Frontend and StorageLayout
pub(crate) enum StorageLayout<'a> { Native, Mixed(&'a MixedStorage), #[cfg(test)] Pure(&'a StorageMap) }
pub(crate) trait Participant<F> {
    fn frontend(&self) -> &Frontend<F>;
    fn storage(&self) -> StorageLayout<'_>;
}
// P: the participant's storage mode, so each step takes only its mode's parts
pub(crate) struct FrontendPart<'a, F, P = CircuitParticipant<F>> { .. }
impl<P: Participant<F>> FrontendPart<'a, F, P> {   // participant, circuits, public inputs
    pub(crate) fn new(participant: &'a P, circuits: &[&'a Circuit<F>],
                      public: &'a [CircuitInput<F>]) -> Result<Self, String>;   // I3: checked once
    pub(crate) fn frontend(&self) -> &'a Frontend<F>;
    pub(crate) fn field(&self) -> &'a F;              // the participant's: every frontend step's field
}
// zk::split: mixed storage, R's bits at its MixedStorage's mask group (I9)
pub(crate) struct MixedSplit<F> { .. }   // a Frontend, its Polygero parameter, its MixedStorage
impl MixedSplit<F> {
    pub(crate) fn new(circuit: &Circuit<F>, map: StorageMap, mask: Group,
                      config: PolygeroConfig, domain: &D) -> Result<Self, String>;
    pub(crate) fn geometry(&self) -> CircuitProofGeometry;
    pub(crate) fn participant(&'a self, domain: &'a D) -> Result<witness_selection::Field<'a, F, D>, String>;
}
// zk::split::pure, tests only until a driver uses it (I11): no parameter, no participant()
pub(crate) struct PureSplit<F> { .. }    // a Frontend and its all-foreign StorageMap
// the joint commitment, crate-private: witness selection, below it, is too;
// L is its field list, (witness_selection::Field, Tail) ... (), witness_selection::Fields
pub(crate) struct JointParam<L: Fields> { .. }
impl<L: Fields> JointParam<L> {
    pub(crate) fn new(fields: L) -> Result<Self, String>;
    pub(crate) fn config(&self) -> PolygeroConfig;
}

// zk, prover: the drivers (`ZkProver`, the composition driver) run these
// crate-private steps; their states are crate-private
impl CircuitParticipant<F> {
    pub(crate) fn prepare(&self, private: Vec<CircuitInput<F>>, rng: &mut impl PrivateRandom)
        -> Result<(CircuitState<'_, F>, Vec<F::E>), String>;  // borrows self
}
impl MixedSplit<F> {
    // mask is R; the witness is [native private inputs | pads | R]
    pub(crate) fn prepare(&self, private: Vec<CircuitInput<F>>, mask: F::E,
                          rng: &mut impl PrivateRandom) -> Result<(SplitState<'_, F>, Vec<F::E>), String>;
    pub(crate) fn foreign_values(&self, pending: &PendingSplit<F::E>) -> Vec<F::E>;  // claim term order, R last
}
impl<L: ProverFields> JointParam<L> {
    // the returned JointProver owns this parameter
    pub(crate) fn commit(self, witnesses: Witnesses<L>, transcript: Transcript,
                         rng: &mut impl PrivateRandom)
        -> Result<(JointProver<L>, PolygeroCommitment, L::Responses), String>;  // I6
}
impl<L: ProverFields> JointProver<L> {
    pub(crate) fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P>;
    // I4: each field's equations, derived on this session; draws the batching weights
    pub(crate) fn finish(self, equations: Statements<L>)
        -> Result<(JointPolygeroProof<Bodies<L>>, Transcript), String>;
}
pub(crate) fn prove(t: &mut Bound<'_, FrontendPart<'_, F>>, state: CircuitState<'_, F>,
                    virtual_inputs: &VirtualInputs<F::E>)    // I4: fixed before the top weights
    -> Result<(CircuitProof<F>, LinearStatement<F::E>), String>;
pub(crate) fn prove_split(t: &mut Bound<'_, FrontendPart<'_, F, MixedSplit<F>>>, state: SplitState<'_, F>)
    -> Result<(SumcheckProof<F>, PendingSplit<F::E>), String>;
pub(crate) struct PendingSplit<E> { pub(crate) claim: SplitClaim<E>, .. }
impl<E> PendingSplit<E> {
    // draws eta (I4), then sends SplitOpening (I9)
    pub(crate) fn open(self, t: &mut Bound<'_, FrontendPart<'_, F, MixedSplit<F>>>)
        -> Result<(E, SplitOutput<E>), String>;
}

// zk, verifier: crate-private steps of the composed and standalone verifiers
impl<L: Fields> JointParam<L> {
    pub(crate) fn receive(self, root: &PolygeroCommitment, responses: L::Responses,
                          transcript: Transcript) -> JointVerifier<L>;    // I6
}
impl<L: Fields> JointVerifier<L> {
    pub(crate) fn bound<'a, P: ?Sized>(&'a mut self, part: &'a P) -> Bound<'a, P>;
    // I4: each field's equations, derived on this session; draws the batching weights
    pub(crate) fn finish<'a, P: JointOpening<Bodies<L>>>(self, equations: Statements<L>,
        proof: Unverified<'a, P>) -> Result<Authenticated<'a, P>, String>; // I7
}
// a complete proof holding a joint opening: ZkProof, ComposedProof, MdocProof
pub(crate) trait JointOpening<B> { fn opening(&self) -> &JointPolygeroProof<B>; }
impl<P> Authenticated<'_, P> {
    // the seal of the proof whose opening this authenticated, on its session (I7)
    pub(crate) fn check_seal(self) -> Result<VerifiedProof, &'static str>;
}
pub(crate) fn reduce(t: &mut Bound<'_, FrontendPart<'_, F>>, proof: &CircuitProof<F>,
                     virtual_inputs: &VirtualInputs<F::E>) -> Result<LinearStatement<F::E>, String>;
pub(crate) fn reduce_split(t: &mut Bound<'_, FrontendPart<'_, F, MixedSplit<F>>>,
                           proof: &SumcheckProof<F>)
    -> Result<SplitClaim<F::E>, String>;
impl<E> SplitClaim<E> {
    // draws eta (I4), then absorbs SplitOpening (I9)
    pub(crate) fn receive(self, t: &mut Bound<'_, FrontendPart<'_, F, MixedSplit<F>>>, mu: &E)
        -> Result<SplitOutput<E>, String>;
}

// zk::split (crate-private), both roles; the draws live in zk::split::transcript (transcript I9)
pub(crate) struct SplitClaim<E> { pub(crate) claim: LinearClaim<E>, .. }  // mixed; rows unbatched
// zk::split::pure, tests only: the pure frontend (pure::prove, pure::reduce) and its batching
pub(crate) struct PureClaim<E> { pub(crate) claim: LinearClaim<E>, .. }   // rows unbatched
impl<E> PureClaim<E> {
    // draws rho = elements(F, L+1) and uses it (I4, I11)
    pub(crate) fn batch(self, t: &mut Bound<'_, FrontendPart<'_, F, PureSplit<F>>>)
        -> Result<ModularClaim<E>, String>;
}
// private to zk::split: nonzero, built only by eta, which open and receive call
struct Eta<E>(..);
fn eta(t: &mut TranscriptRef<'_>, f: &F) -> Eta<F::E>;  // nonzero(F)
#[must_use] pub(crate) struct SplitOutput<E> { pub(crate) statement: LinearStatement<E>,
                                               pub(crate) foreign: ModularClaim<E> }
pub(crate) struct LinearClaim<E> { pub(crate) weights: Vec<E>, pub(crate) target: E }  // zk::batching
#[must_use] pub(crate) struct ModularClaim<E> { pub(crate) terms: Vec<(Group, E)>, pub(crate) target: E }  // zk::storage, crate-private

// zk: standalone single-circuit proof
impl ZkProver<F> {
    pub fn new(circuit: Circuit<F>, config: PolygeroConfig, domain: &D)
        -> Result<Self, String>;
    pub fn statement<'a>(&'a self, context: &'a [u8], public: &'a [CircuitInput<F>])
        -> Result<ZkProofStatement<'a, F>, String>;
    pub fn commit<'s>(&self, private: Vec<CircuitInput<F>>, statement: &'s ZkProofStatement<'s, F>,
                      domain: &'s D, rng: &mut impl PrivateRandom)
        -> Result<ZkProverCommitment<'s, F, D>, String>;  // opens the session, owns the parameter
    pub fn prove(&self, committed: ZkProverCommitment<'_, F, D>)
        -> Result<EncodedProof, String>;               // sealed with the statement's geometry
}
impl ZkVerifier<F> {
    pub fn new(circuit: Circuit<F>, config: PolygeroConfig, domain: &D)
        -> Result<Self, ZkVerificationError>;
    pub fn geometry(&self) -> ZkProofGeometry;
    pub fn statement<'a>(&'a self, context: &'a [u8], public: &'a [CircuitInput<F>])
        -> Result<ZkProofStatement<'a, F>, ZkVerificationError>;
    pub fn verify(&self, session: Opened<'_, ZkProofStatement<'_, F>>,
                  proof: Unverified<'_, ZkProof<F>>, domain: &D)
        -> Result<VerifiedProof, ZkVerificationError>;
}
```

How the API carries the invariants:

- `FrontendPart` is part of the statement, so the circuits, layout and
  public inputs a frontend reads are the ones absorbed (I3, transcript I2).
- `JointParam::commit` and `JointParam::receive` take the `Transcript` by
  value. A frontend can reach the transcript only through the joint handle's
  crate-private `bound()`, after the fingerprint responses (I6).
- `CircuitState` and `SplitState` are move-only and consumed by `prove` or
  `prove_split`, together with the `SumcheckPads` they own, so one set of
  pads masks one proof. Each borrows the participant that prepared it, so
  it cannot outlive it, and records its circuit IDs, profile, circuit
  geometry, input layout and storage map by reference, never by copy.
  `prove` and `prove_split` compare these values with the part's
  participant's: they reject a state that another participant prepared,
  even one over the same circuit with another storage map, and accept one
  from an equal-valued participant.
- `PendingSplit::open` consumes the pending split, draws eta, and returns
  `mu` with both outputs. No call can pair a native row with a claim
  built from another `eta` or `mu` (I9).
- `LinearStatement` has crate-private fields and no digest: only the
  compiler builds frontend rows (I2, I5).

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Absorbing a circuit ID, layout, storage run or public input after the statement | I2: no zk function can write except `send` of its own message |
| Proving one circuit list and committing the layout of another | I3: the layout and circuits come from one `FrontendPart` in the statement |
| Drawing a frontend challenge before the witness is selected | I6: the frontend's `Bound` exists only after commit or receive |
| Drawing eta before the frontend's last message, or reusing it | I4: `open` and `receive` draw it on entry and use it in the same call |
| Drawing the Polygero batching weights before some participant's last frontend message | I4: `finish` draws them, and it takes every field's equations, which exist only after that field's frontend |
| Authenticating a system other than the one the batching weights were drawn for | I4: the weights are drawn inside `finish` for the equations it takes; no caller holds them |
| Opening with equations derived on another session, or a static system | I4: `finish` compares each statement's session stamp with its own |
| Omitting a field's equations | I4: `finish` takes the typed per-field tuple; a shorter one does not compile |
| A zero eta, which would drop the foreign part of the input equation | I4: `Eta` comes only from `nonzero(F)` |
| Native row and modular claim built from different `eta` or `mu` | I9: one call returns both |
| Sending `mu` without absorbing it, or absorbing a different value | I9: `open` and `receive` send `SplitOpening` themselves |
| A pad stored foreign in mixed storage, so a layer row would read a foreign value | I9: `MixedStorage::new` rejects it |
| Two storage maps with the same statement encoding | I10: canonical maximal runs |
| Committing virtual inputs, or letting the primary circuit read them | I8: `InputLayout::new`, `compile_packed` substitution |
| Batching mixed-storage rows, so the native row depends on `rho` | I11: `PureClaim::batch` takes only a `PureSplit`'s part (type) |
| Treating a reduced `LinearStatement` as acceptance | I7: only `Authenticated::check_seal` returns a `VerifiedProof`, and only `finish` returns an `Authenticated` |
| Dropping a coefficient or a zero row when lowering constraints | I5: the compiler keeps every term; compile tests and Lean |
| Reusing a prover state across proofs or participants | `CircuitState` and `SplitState` are consumed; `prove` and `prove_split` compare the participant each recorded with the part's |

## Soundness and zero knowledge

| Check | Purpose | Error | Lean |
|---|---|---|---|
| Fingerprint rows (witness selection) | Fix the committed witness before frontend challenges | 1/#F^2 per candidate pair | `ZkJoint`, `FingerprintRows`, `WitnessSelection.Collision` |
| Sumcheck rows (layer and input) | Reduce circuit satisfaction to affine rows | two roots per round, 2/(#F-1) per terminal, 1/#F per combine | sumcheck-v2 `Challenges.challenge_bad_card_le`, `LinearTerminal` |
| Constraint compiler | Rows hold iff the symbolic constraints hold | none (exact) | `LfzkV2.Compiler.compile_correct`, `compiled_iff_clear` |
| Virtual substitution | Rows over committed inputs equal rows over the full input array | none (exact) | `LfzkV2.InputBinding` |
| Dual packing, `d > 1` | Reduce the input claim to two rows over packed words | 1/#F per packing challenge | dual-packing `Instance.nativeLinearVerify` |
| Split (rescaling) | Native row and modular claim imply the input equation and equal masks | at most one bad nonzero eta: `1/(p-1)` | `Prime.rescaling_bad_card`, `Prime.Claim.true_or_rescaling_bad`, `Handoff.split_handoff` |
| Row batching, pure | One modular claim implies every row | `1/p` for one uniform combination | `RowBatching.bad_probability_le`, `PureHandoff.pure_handoff` |
| Joint authentication | All rows hold on the committed cells | Polygero, `c/q` | joint Polygero, `Soundness.Composition` |

Here `#F` is the order of the participant's field, `q = 2^128` and `p` is
the P-256 coordinate prime. Equality of the binary and prime copies of R is a
conclusion of `Handoff.split_handoff`, not a premise. For mdoc these terms
compose into `Mdoc.Soundness.averaged_ratio_le`. The split's rescaling root
is charged `1/(p-1)` in `ApplicationCharging` (`.rescaling`); row batching
is charged 0 there because mdoc has none.

Zero knowledge:

- Sumcheck messages are masked by committed uniform pads, and the cross pad
  hides the cross coefficient (sumcheck design).
- Packing masks hide `U` and `A`; fingerprint masks hide the fingerprint
  responses.
- `mu = eta*<w_F, v_F> + R` with R uniform in `F_p`. `mu` is the only
  directly published value that R masks, so it is uniform and independent of
  the witness. R also enters the native row and the modular claim, and its
  committed bits feed the adapter; hiding of the whole view rests on the
  joint simulation (`Mdoc.ZeroKnowledge.statClose`), not on R being used
  once. R's prime cell is hidden by Polygero, its bits by the binary
  commitment. Lean `ZeroKnowledge.Frontend.Adapter.Mdoc.coupling_mu` gives
  the coin bijection.
- Virtual inputs and row-batching weights are public functions of the
  transcript; they reveal nothing.
- The frontend adds no statistical term. The complete view is within
  `(Qpre+Qpost)/2^256` of the simulation (`Mdoc.ZeroKnowledge.statClose`);
  the frontend steps are exact coin changes inside
  `StrandCanonicalExactSimulation.ghost_sameDistribution`.

## Open questions

1. **Provenance of virtual inputs.** `VirtualInputs` are plain crate-private
   data; I8 rests on the in-crate caller deriving them from bound values.
   Recommendation: give `VirtualInputs` a constructor that only
   `foreign::adapter` can call, which derives the leaves from the drawn conversion
   pair and the sent `P256AdapterQuotients`.
