# Foreign storage design

Foreign storage lets a prime-field frontend keep some of its values as bits
in the GF(2^128) commitment. The composition driver (`foreign::compose`)
proves one binary host circuit and one P-256 split circuit on one transcript,
under one joint Polygero commitment. The zk layer specifies two storage
shapes for the split circuit: mixed (some values native) and pure foreign (no
native value). The composition driver supports mixed storage only; a
composition with pure-foreign storage is future work (see I2). The zk layer
(`zk::split`) turns the split frontend's claim into a modular claim over
foreign bit groups: for mixed storage by splitting the input equation with
eta and the masked message `mu`, for pure-foreign storage by batching every
row with fresh row weights. The P-256 adapter (`foreign::adapter::p256`)
discharges that modular claim inside the binary host circuit: it publishes
two masked quotients, and its per-proof virtual leaves feed a fixed
product-tree fragment that the host sumcheck proves next to the host
circuit. The driver owns every hand-off between these sub-protocols: it
draws each input challenge (transcript I8) right after the message that
closes the previous sub-protocol. Witness selection opens the composition
with the joint commitment. The joint Polygero opening takes the affine
statements after the last frontend message and batches them with weights it
draws and uses itself. For mdoc, the host is the hash circuit, the split circuit is the
signature circuit with mixed storage, and the application wraps the composed
body in `MDA7` and the seal (transcript I10, I11).

## Statement

Notation: `p` is the P-256 coordinate prime, `M = 2^128 - 1` is the order of
GF(2^128)^*, `Q` is the quotient width, the type parameter of
`P256Mode<Q>`.

**Public.** Everything below is part of the transcript statement
(transcript I1, I3): the host circuit `C_H` over GF(2^128), the adapter
fragment and the split circuit `C_S` over P-256 (one `Circuit` message each,
in that order); the binary and prime `CommitmentLayout` (the prime one
carries the storage map as its native and bit-stored run lists, and R's bit
group, empty for pure-foreign storage); the mode's `AdapterLayout` (see
Formats); the `JointGeometry`; and the public inputs `x_H` (bits, absorbed
as GF(2^128) elements) and `x_S` (P-256 elements).

**Committed.** The joint commitment holds:

| Field | Mixed storage | Pure-foreign storage |
|---|---|---|
| GF(2^128) | `[host private | R bits | O_0 | O_1]`, then sumcheck pads | `[host private | O_0 | O_1]`, then sumcheck pads |
| P-256 | `[native private inputs | sumcheck pads | R]` | nothing; the prime participant is not a joint field |

In mixed storage R is one uniform P-256 element. Its 256 bits are committed
in the binary witness and its value as the last prime cell. In pure-foreign
storage every split value, sumcheck pads included, is a foreign bit group.
`O_0`, `O_1` are the `Otp<Q>` quotient pads.

**Claim proven.** There are private inputs `h` of `C_H` and `s` of `C_S`
such that `C_H(x_H, h)` and `C_S(x_S, s)` hold, where each foreign value of
`s` equals, modulo `p`, the integer whose little-endian bits are its group
in `h`.

**Claim handed on.** Affine statements over the committed cells, which the
joint Polygero opening authenticates:

- binary: the host sumcheck's input claim over `[C_H, fragment]`, with the
  virtual leaves substituted, reduced through dual packing
  (`constraint_compiler::compile_packed`);
- prime, mixed storage only: the split circuit's layer rows on native pads,
  then the native row `eta*<w_N, v_N> - R + mu - eta*t = 0`
  (`split_statement`). Pure-foreign storage hands on no prime statement.

**Adapter sub-statement.** The adapter starts from a `ModularClaim`, fixed
before its first challenge:

```text
mixed:  sum_j c_j * value(G_j) + sum_{r<256} 2^r * R_r = mu      (mod p)
        c_j = eta * w_j      for each foreign value j, in value order
pure:   sum_v c_v * value(G_v)                         = target  (mod p)
        c_v, target          from the row weights, for every value v
```

where `value(G)` is the integer of the bits in group `G`. The pure-foreign
coefficients and target are those of `zk::split::pure_claim`: with layer
rows `A_c*v + b_c = 0` and row weights `rho_0..rho_L`, `c = sum_c rho_c*A_c
- rho_L*w_priv + rho_L*k_pads` and `target = -(sum_c rho_c*b_c + rho_L*t)`.
The target is public. The adapter ends with the fragment's assertions: for
each tree `t` in `{0, 1}`, the product of the tree's virtual leaves is one.
The host sumcheck proves those assertions.

## Invariants

Code comments and the rest of this document cite these as "foreign I1" and
so on.

**I1. The driver owns every cross-protocol hand-off.** Four challenges cross
a sub-protocol boundary inside the composition: the prime top weights, eta
(mixed storage), the conversion pair and the host top weights. The driver
draws each one as a `Challenge<T>`, right after the message that closes the
previous sub-protocol, and hands it to the next. No sub-protocol draws its
own leading challenge; each takes it as an input and `accept`s it
(transcript I8). Two weight vectors cross no boundary, because the step that
draws them uses them in the same call: the pure-foreign row weights
(`SplitClaim::batch`) and the Polygero batching weights (the joint opening,
`JointProver::finish` or `JointVerifier::finish`, on both fields'
statements).
*Enforced by:* the sumcheck, split and adapter entry points take
`Challenge<T>` parameters (type); the stamp check in `accept` rejects a
challenge drawn at the wrong boundary in both roles (runtime); the
role-trace test of I2.

**I2. Both roles run one hand-off schedule, for mixed storage.**
`ComposedStatement::prove` (`compose/prover.rs`) and
`ComposedStatement::reduce_and_authenticate` (`compose/verifier.rs`) make the
same draw calls in the same order: `joint::top_weights` for the prime
frontend, `split::transcript::eta`, `AdapterMode::draw_conversion`,
`joint::top_weights` for the host, then `JointProver::finish` or
`JointVerifier::finish` on both fields' statements. Each draw call only
draws; the sub-protocols send.
The driver always supplies the split mask R, so it composes mixed storage
only. Pure-foreign storage is specified (the zk layer implements its row
batching, and Lean models it as `RowBatching`, `PureHandoff` and
`PureComposition`), but a pure-foreign composition is future work, and no
application may use it until its application model charges those events.
*Enforced by:* `Composition::new` builds the split participant with a mask
group, which `Split::new` rejects for pure-foreign storage (runtime); the
role-trace test (transcript I9); `check_mdoc_round_shapes`.

**I3. Each adapter input is fixed before the challenge that follows it.**
The modular claim is a function of the statement, the split frontend's
messages and the split's challenge (eta, or the row weights the pure split
step draws), plus `mu` for mixed storage. For mixed
storage the conversion pair is drawn after `SplitOpening`; for pure-foreign
storage it is read after the row weights, from the same stream. The virtual
leaves are a function of the claim, the conversion pair and the masked
quotients. The host top weights are drawn after `P256AdapterQuotients`.
Nothing the host sumcheck sends can change a leaf.
*Enforced by:* the claim and leaf functions take only these values
(type); the stamps of the conversion and host top-weight challenges
(runtime); `VirtualInputs::validate` (runtime).

**I4. Two independent full-field rescalings, two trees.** Each conversion
challenge is a uniform nonzero element of `F_p`. Both are read from one
stream, and each rescales the whole claim into its own tree. A false claim
survives one tree with probability about `2^(Q+1-128)`, too much on its own.
*Enforced by:* `Conversion` holds `[P256Element; 2]` and is built only by the
nonzero draw, and the raw encoder `P256Plan::encode`, which takes plain
field elements, is crate-private, so outside tests only `P256Mode` calls it,
with an accepted `Challenge<Conversion>` (type); `P256Plan::TREES = 2` fixes
the fragment's `TreeShape` (constant); `Adapter.two_bad_probability_le` (Lean).

**I5. Quotients are words, published only masked.** The honest quotient
`k_t` is a `Word<Q>`. `Word` is crate-private and exists only in prover
builds, and the quotients are held only in the crate-private
`P256Encoded`, so code outside the crate never sees one; inside the crate,
`P256Mode::prove` masks them before sending. The proof carries
`MaskedWord<Q> = k_t xor o_t`, where `o_t` is an `Otp<Q>` committed in the
binary witness. Each pad is sampled fresh for the proof and masks exactly
one quotient: two words masked with one pad would publish their XOR. The
claim's bit count is at most `2^Q`, so every honest quotient fits.
*Enforced by:* `Word`, `P256Encoded` and `MaskedWord::mask` are
crate-private, and `Word` has no encoder (type); `Otp` is built only by the
prover's `Otp::sample`, which `ComposedStatement::prove` calls through
`sample_pads` for each proof; `Otp` is neither `Copy` nor `Clone`, its
`Debug` omits the value, and `MaskedWord::mask` and `AdapterMode::prove`
consume their pads (type); `P256Plan::new` rejects `bits > 2^Q` (runtime);
mdoc's const assertion `SHARED_BITS + MASK_BITS <= 1 << QUOTIENT_BITS`;
`MaskedWord::read` rejects nonzero padding (runtime).

**I6. The binary input array is fixed and partitioned.** Its layout is

```text
[public | host private | R | O_0 | O_1 | leaves]      ; R is absent for pure-foreign storage
 <---- C_H ninput ---->
         <------ committed ------->
 <------------------ fragment ninput ---------------->
```

The host circuit is archived at its natural width. R and the pads lie in a
`ReservedSuffix` that starts at the host circuit's `ninput`; the leaves
start at the suffix's end. Every foreign group lies in the host private
range. Each sumcheck component reads only its own input prefix, so `C_H`
cannot address R, the pads or the leaves. The mode writes `Q`, the tree
count, the virtual leaf count and the positions of the quotient pads into
the statement as its `AdapterLayout` (transcript I3), from the same
geometry it then uses. R's position is in the split participant's
`CommitmentLayout`.
*Enforced by:* `ReservedSuffix::new(ninput)`, the group check in
`Composition::new` and `InputLayout::new` (runtime); the mode writes
`AdapterLayout` from the geometry it then uses (`AdapterMode::write_layout`);
the sumcheck prefix read (structural); `HashCircuit.readDisjoint` and
`MdocWitness.hashChecks_prefix` (Lean).

**I7. The fragment is fixed and challenge-free.** The fragment holds one
product tree per conversion challenge, and its only constant is one. It is
built by `fragment(npublic, virtual_start, shape)`. Every
challenge-dependent value lives in the virtual leaf definitions, which
constraint compilation substitutes like public inputs and which are never
absorbed (transcript I3). The fragment's circuit ID is in the statement.
*Enforced by:* `fragment` has no challenge parameter (type);
`Adapter.ProductTree.satisfies_iff` and `Adapter.Leaves.tree_product_check`
(Lean).

**I8. R is fresh, used once, and checked only modulo p.** For mixed storage
the prover samples R inside `ComposedStatement::prove`. R enters exactly
two equations: the native row (coefficient `-1` at the R cell) and the
modular claim (coefficients `2^r` on its bits). Its bits carry no range
check, because only their residue modulo `p` enters the claim. Pure-foreign
storage has no R: its claim's target is public, so it hides nothing.
*Enforced by:* R is not a parameter of `ComposedStatement::prove` (type), and
`Split::new` requires R's mask group exactly for mixed storage (runtime);
`Handoff.product_handoff` (Lean) proves that the two copies of R agree
modulo `p` outside the counted rescaling event.

**I9. The body is the send sequence.** The proof body lists the interactive
fields in the order the driver sends them, then the terminal fields. Each
interactive field's wire bytes are exactly the payload of its message
values: `mu` is the 32-byte canonical element of `SplitOpening`, and each
masked quotient is the `ceil(Q/8)`-byte payload of one `Bits(Q)` value.
*Enforced by:* `MdocProof::read` takes its geometry from `Bound` and passes
it to the crate-private `ComposedProof::read` (transcript I2, proto I2); the
trace test `check_trace_matches_wire`, which checks that the absorbed
payloads, in send order, are the interactive section byte for byte.

## Protocol

The composition's part of the challenge schedule. Each row ends with the
draws that follow its messages; *input* draws are made by the driver (I1).

### Mixed storage

| Step | Sub-protocol | Sends | Then draws | Drawn by | Consumer |
|---|---|---|---|---|---|
| 1 | witness selection (opening message) | `Commitment`: Bytes(32) | witness-selection coefficients | witness selection | witness selection |
| 2 | witness selection | `FingerprintResponse` x 2: Elements(GF2_128, 2), Elements(P256, 2) | prime top weights (*input*) | driver | prime sumcheck |
| 3 | prime frontend over `C_S` | per layer: `SumcheckRound` x logw, `SumcheckCross`, `SumcheckClaims` | the sumcheck's own draws; after the last `SumcheckClaims` also eta = `nonzero(P256)` (*input*) | sumcheck; driver | sumcheck; split |
| 4 | split | `SplitOpening`: Elements(P256, 1) mu | conversion pair = `nonzero(P256)` x 2 (*input*) | driver | adapter |
| 5 | adapter | `P256AdapterQuotients`: Bits(Q) m_0, Bits(Q) m_1 | host top weights (*input*) | driver | host sumcheck |
| 6 | host frontend over `[C_H, fragment]`, then binary dual packing | sumcheck messages, `PackingU`, `PackingA` | sumcheck and packing draws; after `PackingA` the Polygero batching weights | host; joint opening | host; joint opening |
| 7 | joint opening | `PolygeroResponse` x 2 | t column indices | joint | Polygero |

Then the terminal fields (Polygero rows, Merkle nonces, frontier count and
frontier) and the
application's seal. The composition contributes two boundaries of its own
(after `SplitOpening` and after `P256AdapterQuotients`); eta reads further
from the node that the prime frontend's last `SumcheckClaims` closes. The
prime participant has packing degree one, so it sends no packing messages.
The batching weights close over every frontend message of both fields:
`PackingA` is the last one.

### Pure-foreign storage

The specified schedule of a composition with pure-foreign storage. No driver
runs it (I2).

| Step | Sub-protocol | Sends | Then draws | Drawn by | Consumer |
|---|---|---|---|---|---|
| 1 | witness selection (opening message) | `Commitment`: Bytes(32) | witness-selection coefficients, binary only | witness selection | witness selection |
| 2 | witness selection | `FingerprintResponse`: Elements(GF2_128, 2) | prime top weights (*input*) | driver | prime sumcheck |
| 3 | prime frontend over `C_S` | per layer: `SumcheckRound` x logw, `SumcheckCross`, `SumcheckClaims` | the sumcheck's own draws; after the last `SumcheckClaims` the row weights = `elements(P256, L+1)`, then the conversion pair = `nonzero(P256)` x 2 (*input*) | sumcheck; split; driver | sumcheck; split; adapter |
| 4 | adapter | `P256AdapterQuotients`: Bits(Q) m_0, Bits(Q) m_1 | host top weights (*input*) | driver | host sumcheck |
| 5 | host frontend over `[C_H, fragment]`, then binary dual packing | sumcheck messages, `PackingU`, `PackingA` | sumcheck and packing draws; after `PackingA` the Polygero batching weights | host; joint opening | host; joint opening |
| 6 | joint opening | `PolygeroResponse` | t column indices | joint | Polygero |

The split sends nothing: the row weights and the conversion pair read
further from the node that the prime frontend's last `SumcheckClaims`
closes (transcript I7). If `C_S` has zero layers, its frontend sends nothing
too, and these draws continue the node closed by `FingerprintResponse`. The
composition contributes one boundary of its own, after
`P256AdapterQuotients`.

### Computation at each step

**Split, mixed.** From the prime frontend's constraints, `split_claim`
forms the input equation `<w, v> = t` over `[private inputs | pads]`.
Given eta:

```text
mu        = eta * sum_{j foreign} w_j * v_j  +  R
claim     = { terms: [(G_j, eta*w_j) for foreign j, in value order] ++ [(G_R, 1)],
              target: mu }
native    = eta*<w_N, v_N> - R + mu - eta*t = 0
```

The prime statement is the layer rows, which read only native pads, then
the native row. They go to Polygero unbatched.

**Split, pure foreign.** Given the row weights `rho_0..rho_L`, `pure_claim`
batches the `L` layer rows and the input equation into one claim (see
Statement) with terms `(G_v, c_v)` for every value in value order and a
public target. There is no prime statement.

**Adapter.** For the instance, let `bits` be the claim's total width (the
foreign widths, then 256 for R in mixed storage), and `X` the
polynomial-basis element encoded as integer 2. The generator is
`g = X^(M - 2^64)`, so `g^(-p) = X`. For each tree `t` with conversion
challenge `gamma_t` (`alpha` in the code), and the claim's target `T`
(`mu`, or the public target):

```text
A_{t,i}   = canonical(gamma_t * c_j * 2^r mod p)     for bit i = bit r of group j
C_t       = canonical(gamma_t * T)
k_t       = (sum_{i : b_i = 1} A_{t,i} - C_t) / p     honest only; 0 <= k_t < bits <= 2^Q
m_t       = k_t xor o_t
```

The tree's leaves, in order, are one data leaf per claim bit and one
quotient leaf per quotient bit:

| Leaf | Definition | Value on committed bit `x` |
|---|---|---|
| data, bit `i` | `Leaf::data(source_i, g^A - 1)`: `1 + (g^A - 1)*x` | `g^(A*b_i)` |
| quotient, bit `j` | `Leaf::quotient(pad_j, X^(2^j), m_j)`: constant `X^(2^j)` if `m_j` else 1, coefficient `X^(2^j) - 1` | `X^(2^j*(m_j xor o_j))` |

`virtual_inputs` multiplies leaf 0's constant and coefficient by
`g^(-C_t)` and emits the leaves tree-major. The fragment then asserts, per
tree,

```text
prod_i (1 + b_i*(g^A_{t,i} - 1)) * prod_j X^(2^j*k_j) * g^(-C_t) = 1,
```

which holds exactly when `M` divides `sum_i A_{t,i} b_i - p*k_t - C_t`
(`Adapter.product_check_iff`). The exponents are reduced modulo `M`
(`integer::reduce_exponent`) and raised through a fixed-base table of
`g^(2^i)` for the 128 bit positions, one multiplication per set bit; a
coefficient's powers for its later bits follow by squaring, with a factor
`X` whenever doubling `A` wraps past `p`.

**Fragment.** For `TreeShape { trees, leaves }`, each reduction layer pairs
adjacent wires within each tree (an odd last wire passes through linearly)
while more than two remain; the output layer computes `l*r + 1` per tree and
asserts it zero. All terms use the constant one.

**Verifier.** It replays the schedule with the proof's values and checks:

- parsing against the absorbed geometry, with canonical masked words (I5);
- the prime frontend's sumcheck, which yields the split claim;
- `P256Plan::encode`: the claim's term widths equal the plan's widths;
- the leaf definitions: count and sources match the input layout
  (`VirtualInputs::validate`), and every target is nonzero;
- the host sumcheck over `[C_H, fragment]`, with the leaves substituted;
- the joint opening of the affine statements, then the application's seal.

The verifier never checks a tree directly: the host statement includes
the tree checks, beside `C_H`, so it implies them.

### mdoc instance

mdoc uses mixed storage.

| Quantity | Value |
|---|---|
| Foreign values | 768 groups of width 1 (issuer digest, device x, device y) |
| Claim bits | 768 + 256 (R) = 1024 = 2^10 |
| `Q` (`QUOTIENT_BITS`) | 10 |
| Trees; leaves per tree | 2; 1024 + 10 = 1034 |
| Virtual inputs | 2068 |
| Fragment layers | 11 |
| `mu` on the wire | 32 bytes |
| Masked quotients on the wire | 2 x 2 bytes |

## Formats

### Transcript messages

All three messages follow the transcript grammar (transcript I5, I6); every
integer is u64 little endian. `AdapterLayout` is a statement message, written
once by the mode; the other two are prover messages.

```text
AdapterLayout        := u64(22) bytes(mode_id) nats(Q, trees, leaves_per_tree)
                        nats(o0_start, Q, o1_start, Q)
SplitOpening         := u64(64) u64(2) u64(1) u64(1) elem_p256            ; Elements(P256, 1): mu
P256AdapterQuotients := u64(65) u64(3) u64(Q) word u64(3) u64(Q) word     ; Bits(Q), Bits(Q): m_0, m_1
bytes(b)             := u64(0) u64(len b) b
nats(x..)            := u64(1) u64(count) u64(x)..
elem_p256            := byte{32}                                          ; canonical, little endian
word                 := byte{ceil(Q/8)}                                   ; LSB first, zero padding
```

`u64(1)` after the kind is FieldID `P256`. `SplitOpening` exists only for
mixed storage.

`AdapterLayout` values for `P256Mode<Q>`, from `P256Mode::new`. Positions
are host input indices. The split mask R is not listed: its bits are in the
split participant's `CommitmentLayout` (transcript I3), at `r_start`, width 256
for mixed storage:

| Value | Mixed storage | Pure-foreign storage | mdoc |
|---|---|---|---|
| `mode_id` | `b"longfellow/v2/foreign/p256/two-full-field-trees/v1"` (`P256_MODE_ID` in `runtime/v2/foreign/adapter/transcript.rs`) | same | same |
| `Q` | the type parameter | same | 10 |
| `trees` | `P256Plan::TREES` | same | 2 |
| `leaves_per_tree` | `bits + Q`, `bits` the claim's total bit width including R's 256 (`P256Plan::shape`); `virtual_inputs()` is `trees` times this | `bits + Q`, no R | 1034 = 768 + 256 + 10 |
| `o0_start` | `r_start + 256`, `r_start = C_H.ninput` | `C_H.ninput` | 271747 for one attribute (`r_start` = 271491) |
| `o1_start` | `o0_start + Q` | `o0_start + Q` | `o0_start + 10` |

The virtual leaves start at `o1_start + Q` (271767 in mdoc), which the fragment's
`Circuit` message confirms through its input count. No domain string or
round label is absorbed. The claim, the row-batched coefficients, the leaf
definitions, the quotients and the generator are derived values and are
never absorbed (transcript I3).

### Proof body

`ComposedProof`, parsed against `ComposedGeometry` taken from `Bound`
(I9, transcript I2). The body is in send order. `ComposedProof` is the
mixed body; the pure body is the specified layout of a future pure-foreign
composition:

```text
mixed      := root fp_host fp_split split_sc mu quotients host_sc host_pack polygero
pure       := root fp_host          split_sc    quotients host_sc host_pack polygero
root       := byte{32}                                   ; Commitment
fp_host    := elem_gf2{2}                                ; FingerprintResponse, binary
fp_split   := elem_p256{2}                               ; FingerprintResponse, prime
split_sc   := sumcheck(g.split().sumcheck())             ; prime frontend; packing degree 1, no packing bytes
mu         := elem_p256                                  ; SplitOpening
quotients  := word word                                  ; P256AdapterQuotients: m_0, m_1
host_sc    := sumcheck(g.host().sumcheck())              ; host frontend over [C_H, fragment]
host_pack  := elem_gf2{g.host().packing_degree()} elem_gf2 ; PackingU, then PackingA
polygero   := joint_polygero(g)                          ; responses, then terminal fields; one field when pure
elem_gf2   := byte{16}
```

`sumcheck` and `joint_polygero` are defined by their own protocols. Every
length is fixed by the geometry, except the frontier, whose count is the
only integer in the body (inside `joint_polygero`, proto I3).

### Words

`MaskedWord<N>` is an element of GF(2)^N. Its encoding is `ceil(N/8)` bytes,
bit `j` at bit `j % 8` of byte `j / 8`, unused high bits zero. The same
bytes are the payload of its `Bits(N)` value. `Otp<N>::sample` reads exactly
`ceil(N/8)` fresh bytes and keeps the low `N` bits.

## Rust API

```rust
// runtime::v2::foreign::compose
pub struct Composition<'a, const W: usize, F, DH, DS, M> { .. }
impl<'a, const W: usize, F, DH, DS, M: AdapterMode<F>> Composition<'a, W, F, DH, DS, M> {
    // Derives participants, reserved suffix and mode from the trusted circuits
    // and storage map; the statement's geometry messages are written from it.
    // Mixed storage only: the split participant always gets R's mask group (I2).
    pub fn new(host_circuit: &'a Circuit<Gf2_128Field>, split_circuit: &'a Circuit<F>,
               storage: StorageMap, joint: PolygeroConfig,
               domains: (&'a DH, &'a DS)) -> Result<Self, String>;
    pub fn geometry(&self) -> Result<ComposedGeometry, String>;
    pub fn statement<'s, I: SetupMessage>(&'s self, identity: I,
        host_public: &'s [CircuitInput<Gf2_128Field>], split_public: &'s [CircuitInput<F>])
        -> Result<ComposedStatement<'s, W, F, DH, DS, M, I>, String>;
    pub fn reserved(&self) -> &ReservedSuffix;
    pub fn mode(&self) -> &M;
}
// The composition's statement: the application's identity message, both
// frontend parts and the geometry the proof is parsed against (transcript I1).
pub struct ComposedStatement<'s, const W: usize, F, DH, DS, M, I> { .. }
impl ComposedStatement<'_, W, F, DH, DS, M, I> {
    pub fn geometry(&self) -> &ComposedGeometry;
    // compose/prover.rs and compose/verifier.rs: no public-input, circuit or
    // geometry parameter (transcript I2); the caller seals afterwards.
    pub fn prove(session: Opened<'_, Self>,
                 host_private: Vec<CircuitInput<Gf2_128Field>>,
                 split_private: Vec<CircuitInput<F>>, rng: &mut impl PrivateRandom)
        -> Result<(ComposedProof<2, Gf2_128Field, W, F, M::Message>, Transcript), String>;
    // Not complete verification: the caller checks the complete proof's seal
    // on the returned transcript (mdoc's run_mdoc_verifier).
    pub(crate) fn reduce_and_authenticate(session: Opened<'_, Self>,
        proof: &ComposedProof<2, Gf2_128Field, W, F, M::Message>)
        -> Result<Transcript, String>;
}
impl Opened<'_, ComposedStatement<'_, ..>> {
    pub fn geometry(&mut self) -> Bound<'_, ComposedGeometry>;   // for MdocProof::read
}

// runtime::v2::foreign::adapter
pub trait AdapterMode<F: SerializableField>: Sized {
    const MASK_BITS: usize;                 // width of R's group, mixed storage
    type Pads;                              // committed one-time pads, prover only
    type Message: AdapterMessage;           // P256Mode: [MaskedWord<Q>; 2], tag P256AdapterQuotients
    type Conversion;                        // the input challenge, nonzero by construction
    fn new(widths: Vec<usize>, npublic: usize, suffix: &mut ReservedSuffix) -> Result<Self, String>;
    fn fragment(&self) -> &Circuit<Gf2_128Field>;
    fn virtual_inputs(&self) -> usize;
    fn write_layout(&self, h: &mut Header<'_>);   // AdapterLayout, from the mode's own geometry (I6)
    fn draw_conversion(t: &mut Bound<'_, Self>, f: &F) -> Challenge<Self::Conversion>;  // called by compose
    #[cfg(any(test, feature = "prover"))]
    fn sample_pads(&self, rng: &mut impl PrivateRandom) -> Self::Pads;
    #[cfg(any(test, feature = "prover"))]
    fn write_pads(&self, pads: &Self::Pads, reserved: &mut ReservedWitness<'_>) -> Result<(), String>;
    // Accepts the conversion, sends Message, returns the leaves (I3).
    #[cfg(any(test, feature = "prover"))]
    fn prove(t: &mut Bound<'_, Self>, claim: &ModularClaim<F::E>, values: &[F::E],
             pads: Self::Pads, conversion: Challenge<Self::Conversion>, f: &F, gf2: &Gf2_128Field)
        -> Result<(Self::Message, VirtualInputs<Gf2_128>), String>;
    #[cfg(any(test, feature = "verifier"))]
    fn verify(t: &mut Bound<'_, Self>, claim: &ModularClaim<F::E>, message: &Self::Message,
              conversion: Challenge<Self::Conversion>, f: &F, gf2: &Gf2_128Field)
        -> Result<VirtualInputs<Gf2_128>, String>;
}
pub struct TreeShape { pub trees: usize, pub leaves: usize }
pub struct Leaf { pub source: usize, pub constant: Gf2_128, pub coefficient: Gf2_128 }
pub struct TreeInstance { pub leaves: Vec<Leaf>, pub target: Gf2_128 }
pub fn virtual_inputs(shape: TreeShape, trees: Vec<TreeInstance>, f: &Gf2_128Field)
    -> Result<VirtualInputs<Gf2_128>, String>;
pub fn fragment(npublic: usize, virtual_start: usize, shape: TreeShape)
    -> Result<Circuit<Gf2_128Field>, String>;            // no challenge parameter (I7)

// runtime::v2::foreign::adapter::p256
pub struct Conversion(/* [P256Element; 2], crate-private */);  // only the nonzero draw builds it (I4)
impl Conversion { pub fn values(&self) -> &[P256Element; 2]; }
pub struct P256Plan<const Q: usize> { .. }              // TREES = 2; new rejects bits > 2^Q (I5)
impl<const Q: usize> P256Plan<Q> {
    pub fn new(widths: Vec<usize>) -> Result<Self, String>;
    pub fn shape(&self) -> TreeShape;
    // crate-private: plain challenges; P256Mode passes the accepted Conversion (I4)
    pub(crate) fn encode(&self, claim: &ModularClaim<P256Element>, alpha: &[P256Element; 2],
        values: Option<&[P256Element]>, p: &P256Field, f: &Gf2_128Field)
        -> Result<P256Encoded<Q>, String>;
}
pub(crate) struct P256Encoded<const Q: usize> { .. }    // leaf coefficients, targets, prover quotients
pub struct P256Mode<const Q: usize> { .. }              // AdapterMode<P256Field>, MASK_BITS = 256;
                                                        // mode ID P256_MODE_ID in adapter/transcript.rs

// runtime::v2::foreign::word (I5)
pub(crate) struct Word<const N: usize>(u64);            // prover builds only; no encoder
pub struct Otp<const N: usize>(u64);                    // built only by Otp::sample; not Copy or Clone
impl<const N: usize> Otp<N> {
    pub fn sample(rng: &mut impl PrivateRandom) -> Self;  // prover builds only
    pub fn bits(&self) -> impl Iterator<Item = bool> + '_;
}
impl<const N: usize> Debug for Otp<N> { .. }            // prints "Otp { .. }", never the value
pub struct MaskedWord<const N: usize>(u64);             // the only word in a proof
impl<const N: usize> MaskedWord<N> {
    pub const BYTES: usize = N.div_ceil(8);
    pub(crate) fn mask(k: Word<N>, o: Otp<N>) -> Self;   // prover; consumes the pad: one pad, one word
    pub fn bit(self, j: usize) -> bool;                  // feeds Encoder::bits
    pub fn encoded(&self) -> Vec<u8>;
    pub(crate) fn read(bytes: &mut &[u8]) -> Result<Self, String>;  // rejects nonzero padding
}
// [MaskedWord<N>; 2] implements AdapterMessage and the sealed reader (proto I2)
```

The split's side is owned by `zk::split` and called by the driver. For mixed
storage, the prover's `PendingSplit::open` accepts `Challenge<Eta<F::E>>`,
sends `SplitOpening` and returns `mu`, the `ModularClaim` and the prime
statement; the verifier's `SplitClaim::receive` accepts the same challenge
and sends the proof's `mu`. For pure-foreign storage, `SplitClaim::batch`
draws the row weights (`elements(F, L+1)`) and uses them, sends nothing and
returns the `ModularClaim` with its public target. `Eta<E>` has no public
constructor; `zk::split::transcript::eta` (a `nonzero(F)` draw) builds it.
The
driver draws both top weights with `zk::joint::top_weights` on the receiving
frontend's `Bound`.

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Drawing the conversion pair before `mu` is sent | I1: `accept` sees a message sent since the stamp and fails in both roles |
| Drawing the host top weights before the masked quotients | I1: the same stamp check |
| A sub-protocol drawing its own leading challenge | I1, I2: entry points take `Challenge<T>`; the role-trace test compares both roles' traces |
| Batching mixed-storage rows, or splitting pure-foreign storage with eta | I2: the driver composes mixed storage only; `SplitClaim::batch` rejects mixed storage, and only `open` and `receive` take `Eta` |
| Leaves that depend on the host sumcheck's challenges | I3: leaves are computed before the host top weights are drawn, from the claim, conversion and message only |
| A zero conversion challenge or eta | I4: `Conversion` and `Eta` exist only from `nonzero` draws |
| Encoding with caller-chosen conversion challenges, such as one repeated | I4: `P256Plan::encode` is crate-private; `P256Mode` passes only the drawn `Conversion` |
| One tree instead of two | I4: `P256Plan::TREES` and `[_; 2]` arrays fix the shape |
| A quotient wider than its word, or a claim too wide for `Q` | I5: `Word::new`, `P256Plan::new`, mdoc's const assertion |
| Publishing an unmasked quotient | I5: `Word` is crate-private and has no encoder or `Message` impl |
| Masking two quotients with one pad, or printing a pad | I5: `MaskedWord::mask` consumes its `Otp`, which is not `Copy` or `Clone`; its `Debug` omits the value |
| Two encodings of one masked word | I5, I9: `MaskedWord::read` rejects padding bits; the Bits payload is the wire bytes |
| The host circuit reading R, a pad or a leaf | I6: reserved bits start at its `ninput`; sumcheck prefix reads |
| A foreign group in the public prefix or outside the host circuit | I6: `Composition::new` rejects it |
| A mode whose geometry differs from the absorbed one | I6: the mode writes `AdapterLayout` from its own geometry |
| A leaf whose source is public or virtual | `VirtualInputs::validate` and `compile_packed` reject it |
| A per-proof circuit | I7: `fragment` takes no challenge; its ID is in the statement |
| Reusing R, or a caller-chosen R | I8: R is sampled inside `ComposedStatement::prove` |
| A foreign sumcheck pad in mixed storage | `Split::new` rejects it: mixed storage keeps every pad native |
| A mask without native values, or native values without a mask | `Split::new`: a mask is required exactly when some values are native |
| Tree sizes that overflow | `TreeShape::virtual_inputs` uses `checked_mul`; `fragment` bounds the width by `u32::MAX` |
| Prover-only data in a verifier build | `Word`, `Otp::sample`, `MaskedWord::mask`, `sample_pads`, `write_pads`, `prove` and quotient accumulation are `cfg(prover)` |

## Soundness and zero knowledge

### Soundness

| Check | What it rules out | Error | Lean |
|---|---|---|---|
| Split with nonzero eta (mixed) | a false input equation, or binary and prime copies of R that differ, surviving the native row | at most one bad eta among `p - 1`: `1/(p-1)` | `Prime.rescaling_bad_card`, `Prime.Claim.true_or_rescaling_bad` |
| Row batching (pure foreign) | a false layer row or input equation surviving one uniform combination of the `L+1` rows | `1/p` | `RowBatching.bad_probability_le`, `PureHandoff.pure_handoff`, `PureHandoff.bad_probability_le` |
| Two conversion trees | a false modular claim whose rescaled sums collide modulo `M` | `(2*floor(K*p/M) + 1)^2 / (p-1)^2` with `K = 2^Q`, quotients adaptive to both challenges; mdoc: at most `4198401 / 2^256`, about `2^-234` | `Adapter.two_bad_probability_le`, `Adapter.Mdoc.conversion_probability_le` |
| Tree product equals one | the product equation is exactly divisibility by `M` | none (exact) | `Adapter.product_check_iff`, `Adapter.Leaves.tree_product_check`, `Adapter.ProductTree.satisfies_iff` |
| Generator | `g` has order `M` and `g^(-p) = X` | none (exact) | `Adapter.Mdoc.generator_order`, `Adapter.Mdoc.quotient_base` |
| Host sumcheck over `[C_H, fragment]` | false trees or a false host circuit | the sumcheck's own terms | `Adapter.Fragment`, `ConcreteAdapterTopology` |
| Joint opening | statements that do not hold on the committed cells | Polygero's terms | Polygero modules |

For mixed storage, `Handoff.product_handoff` and `Handoff.split_handoff`
combine the rows: either the claim is true and both copies of R agree modulo
`p`, or the rescaling event or the conversion event occurred.
`Application.Bad` lists these events beside the circuit, packing and backend
events, and `Mdoc.Soundness.averaged_ratio_le` is the endpoint. The per-tree
error is about `2^(Q+1-128)` (`2^-117` for mdoc); the two independent trees
square it (I4). The composition's boundaries enter the endpoint bound only
through the boundary count `r`, as `r/2^256`. Read separation of the host
circuit is a theorem (`HashCircuit.readDisjoint`,
`MdocWitness.hashValid_of_satisfies`), so no challenge can change the
ordinary host predicate.

For pure-foreign storage, `PureHandoff.pure_handoff` combines the rows as
`Handoff.split_handoff` does for mixed storage: either every row holds on the
decoded foreign values, or the row-batching event (error `1/p`,
`RowBatching.bad_probability_le`) or the conversion event occurred. The row
weights are read before the conversion pair, so the claim is fixed when the
conversion challenges are read and the conversion bound applies unchanged:
`PureHandoff.bad_probability_le` bounds that answer's joint error by
`1/p + (2*floor(K*p/M)+1)^2/(p-1)^2`, and `PureComposition.rows_reduction`
composes it with both frontends as `Composition.rows_reduction` does. No
application may use pure-foreign storage until its application model lists
these events beside its circuit, packing and backend events and charges them
in its schedule, as `Application.Bad` and `ApplicationCharging` do for mdoc.

The Lean model fixes the field pair and the budget to mdoc
(`Adapter.Mdoc.inputBits = 768 + 256`, `quotientBound = 2^10`).

### Zero knowledge

| Published value | Why it reveals nothing | Lean |
|---|---|---|
| `mu` (mixed) | R is uniform in `F_p`, and `mu` is the only directly published value it masks, so `mu` is uniform and independent of `<w_F, v_F>`. R also enters the native row and the modular claim, and its bits feed the adapter (I8); hiding of the whole view rests on the joint simulation, not on R being used once | `Mdoc.ZeroKnowledge.statClose` |
| claim target (pure) | a public function of the statement, the frontend's messages and the row weights | none needed |
| `m_t` | `o_t` is uniform in GF(2)^Q and used only here, so `k_t xor o_t` is uniform | `FrontendAdapterBits.rawOtpEquiv` |
| Leaf definitions | public functions of public values; never absorbed | `Adapter.Leaves` |
| R bits, pads, foreign split values | committed; hidden by the joint commitment | `StrandCanonicalCommitmentHiding` |

Ordinary host validity holds under every assignment of R, the pads and the
leaves (`MdocWitness.uniformHashValid_of_valid`), so the simulator needs no
witness for them. The complete mdoc bound is `(Qpre+Qpost)/2^256`
(`Mdoc.ZeroKnowledge.statClose`).

## Open questions

1. **Second application on the same adapter.** JWT and other planned
   applications have a different shared-bit count, while the Lean
   instantiation hard-codes `768 + 256` bits and `K = 2^10`.
   Recommendation: state `Adapter.Mdoc.conversion_probability_le` for any
   `bits <= 2^Q` and instantiate it per application, before the second
   application lands.
