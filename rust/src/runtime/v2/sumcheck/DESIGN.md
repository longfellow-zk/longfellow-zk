# Longfellow v2 layered sumcheck design

The layered sumcheck reduces the claim "these circuits are satisfied by the
committed inputs" to affine equations in committed cells. It runs once per
field participant: over GF(2^128) for the host (the hash circuit composed
with the adapter fragment) and over the P-256 base field for the signature
circuit. One run treats an ordered list of same-field circuits as a single
layered circuit, from outputs to inputs, with one global wire array per
layer. Every transmitted value is masked by a committed pad. The verifier
never checks a value numerically; it derives equations that Polygero later
authenticates against the joint commitment.

In the v2 stack, the prime sumcheck follows witness selection and the host
sumcheck follows the adapter. Each takes its first challenge, the top
weights, from the boundary its predecessor closed (transcript I8). Its output
goes to the constraint compiler (`runtime::v2::zk::constraint_compiler`) and
from there to dual packing (host) or the split (prime), then to Polygero.

## Statement

**Input claim.** The transcript statement (transcript I1, I3) fixes, for one
participant over field F:

| Item | Meaning |
|---|---|
| circuits `C_0..C_{n-1}` | `core::proto::v2::Circuit<F>` values in statement order, each with its ID |
| `N = max_c ninput_c` | width of the one shared input array `W` |
| `npub` | common public prefix length; equal in every circuit |
| `x` in F^npub | the participant's `PublicInputs` |

Before this frontend's first sumcheck challenge, the private inputs and the
pads of this run are committed, and the virtual input definitions (public
affine functions of committed cells) are derived from the preceding
transcript and fixed. The input array is `W = [x | private | virtual]`.
The claim is: for every circuit `c`, evaluating `C_c` on `W[0..ninput_c]`
gives zero on every output and satisfies every assertion.

**Output claim.** With `L` stages (the depth of the deepest circuit), the run
produces `Constraints<F::E>` (`sumcheck/symbolic.rs`):

| Equation | Form |
|---|---|
| stage `s`, for `s` in `0..L` | `C_s(pads) + r_s*(d_s + p_D,s) + r_s^2*p_AB,s - m_A,s*m_B,s = 0` |
| input | `input_claim(pads) - sum_{i<N} omega_i * W[i] = 0` |

`C_s` is stage `s`'s running claim after its rounds. Each left side is an
affine `PadExpression`: a public constant plus public
coefficients on named `Pad` cells, and for the input equation the dense
public weights `omega` (`input_weights`, length `N`). Soundness: if some
circuit is not satisfied at `W`, then for every assignment of the committed
cells some equation fails, except on the bad challenge events listed under
Soundness.

## Circuit format consumed

Only these parts of `core::proto::v2` matter to the protocol.

| Field | Use |
|---|---|
| `Circuit::id` | absorbed in the statement; never by sumcheck |
| `RawCircuit::{ninput, npublic_input, noutput}` | input prefix, public prefix, output count |
| `RawCircuit::constants` | coefficient table, indexed by `k` |
| `RawCircuit::layers[j]` | `j = 0` at the outputs; `nw` is the layer's input width, `logw = ceil_log2(nw)` |
| `Layer::{quadratic, linear, constant}` | streams of `(g,l,r,k)`, `(g,l,k)`, `(g,k)` records |
| `Layer::assertion_counts(&classes)` | `[quadratic, linear]` records whose coefficient is zero, derived from `classify_constants`; never stored |

Layer `j` has `noutput` outputs if `j = 0`, else `layers[j-1].nw`. Its output
`g` is

```text
V[g] = sum_{(g,l,r,k)} constants[k]*W[l]*W[r]
     + sum_{(g,l,k)}   constants[k]*W[l]
     + sum_{(g,k)}     constants[k].
```

A quadratic or linear record with `constants[k] = 0` is an assertion:
`W[l]*W[r] = 0` or `W[l] = 0`. It contributes nothing to `V`. Constant
records have nonzero coefficients (the LFC3 reader rejects zero). Each run
classifies the table once (`classify_constants`: `Zero`, `One`, `MinusOne`,
`General`; in characteristic two minus one is `One`) and splits each layer
into eleven streams (`sumcheck/split.rs`): four quadratic, four linear, three
constant. The split changes traversal cost only, never the arithmetic or the
circuit ID.

## Composition: stages and fragments

`Schedule::new` (`sumcheck/fragments.rs`) is the only constructor of the
global layout. It orders circuits by decreasing depth, ties broken by
statement index, and aligns them at their inputs: circuit `c` with
`d_c = layers.len()` is active at stages `L - d_c .. L`.

| Quantity | Stage `s < L-1` | Stage `L-1` (inputs) |
|---|---|---|
| fragment input range of `c` | concatenated, no padding: `off_c .. off_c + nw` | `0 .. ninput_c` (overlapping) |
| `nw_s` | sum of active widths | `N` |
| fragment output range | concatenated: carried outputs first, then entering outputs | same |
| `nv_s` | `nw_{s-1}` carried + `e_s` entering outputs | same |
| `logw_s` | `ceil_log2(nw_s)` | `ceil_log2(N)` |

A circuit enters at the stage where its layer 0 is active; its `noutput`
outputs join the tail of the output array and receive fresh weights. A
circuit with zero layers asserts that its input prefix `W[0..ninput_c]`
vanishes (its outputs are its inputs, so `noutput = ninput`). `Schedule::new`
rejects an empty list, unequal `npublic_input`, `npublic_input > ninput_c`,
a last layer whose `nw` differs from `ninput_c`, a zero-width layer, width
overflow, and a `logw_s` that is not sane (`core::proto::sane_logw`: above
`MAX_LOGW = 40`, or not below `usize::BITS`). The result carries
`SumcheckProofGeometry { logw_layers }`. Nothing about fragments is
transmitted: the rounds, terminal and combine act on the global arrays only.

## Invariants

Code comments and other design documents cite these as "sumcheck I1" and so
on.

**I1. The instance is fixed before the first sumcheck challenge.** Circuits,
their order and public inputs come from the frontend's
`Bound<'_, FrontendPart>` (transcript I2), and the schedule is derived from
those circuits. Committed inputs, virtual input definitions and pads are
fixed by earlier messages or are arguments of the call. Each entry point
draws the top weights itself, on entry (`Schedule::draw_top`), from the
boundary that follows the last message fixing the instance. Sumcheck absorbs
nothing but its own three message kinds.
*Enforced by:* the sumcheck entry points are crate-private and called only
by the zk frontends, which read the circuits from their `Bound`, so no
public prove or verify function takes a circuit, public-input or geometry
parameter (type); each entry point builds its schedule from the circuits
it takes and draws the top weights from that schedule, so no top weights of
another schedule, boundary or session reach it (type, transcript I8).

**I2. Both roles run one stage schedule.** Each stage sends
`logw_s` x `SumcheckRound`, then `SumcheckCross`, then `SumcheckClaims`; it
draws `z` after each round, `r != 0` after the cross message, and `alpha`
followed by the next stage's weights after the claims. The cross message
precedes `r`, and both claims precede `alpha`. Every boundary closes a node
with a prover message (transcript I7).
*Enforced by:* the prover and the verifier each run their own stage loop
(`prove_split` in `sumcheck/prover.rs`, `derive_constraints_for_circuits`
in `sumcheck/verifier.rs`), and both loops make every send and draw
through the same shared steps: `round_challenge`, `terminal_challenge` and
`end_layer` in `sumcheck/transcript.rs`, and the `Schedule` methods
`draw_top`, `enter`, `after_combine` and `finish_inputs`; the role-trace
test (transcript I9);
`terminal_transcript_fixes_cross_before_scale_and_claims_before_combination`
(test); `LfzkV2.Current.Schedule` (Lean).

**I3. One global layer, one round polynomial.** A stage has one witness array,
one `q_l`, one monomial array `m(u)` and one `q_r`, indexed by the global
wire index. Fragments only translate sparse gate indices through their
ranges. Circuit boundaries add no coordinate, claim or challenge.
*Enforced by:* `Schedule::new` is the only source of ranges (type);
`quad_fragments_match_a_physically_merged_circuit` (test).

**I4. Every zero assertion has its own independent weight.** Each entering
output receives a fresh weight at its stage, including scalar outputs. Each
assertion record receives a fresh coefficient that replaces its entire
output-weighted coefficient, so no output weight can cancel it; draw order is
quadratic records across fragments, then linear records. Each zero-layer
circuit receives `ninput_c` fresh weights on its prefix. Every weight is
drawn after the values it weights are committed and before the stage that
uses it sends its first message.
*Enforced by:* `Schedule::draw_top` and `Schedule::after_combine`, through
`Schedule::draw_stage` and `Schedule::input_assertions`, are the only
producers (type); `output_sampling_uses_independent_weights_*`,
`functional_transition_and_independent_assertions_*`,
`early_output_weights_cannot_hide_a_false_*`,
`single_hand_rejects_a_false_internal_assertion` (tests); `LfzkV2.Native`
(Lean).

**I5. A circuit reads only its own input prefix.** At the input stage every
fragment addresses `W[0..ninput_c]`. A circuit cannot read the suffix that
holds data other circuits must not influence (the split mask R, adapter pads,
virtual leaves).
*Enforced by:* `Schedule::new` sets the range from `ninput_c` (runtime);
`components_read_prefixes_of_one_shared_input_array` (test);
`HashCircuit.readDisjoint` (Lean, for the typed hash topology).

**I6. Every transmitted value is masked by a one-time committed pad.** Round
messages are `c0 - s0, c1 - s1`. The cross message is
`d = A*p_B + B*p_A - p_D`. The claims are `A + r*p_A, B + r*p_B` with
`r != 0`. All pads are sampled with `PrivateRandom` before the commitment,
and `p_AB = p_A*p_B`. A pad set masks exactly one run.
*Enforced by:* `SumcheckPads` is a crate-private type distinct from
`SumcheckProof`, is not `Clone`, and `evaluate_and_prove_circuits` consumes
it (type; test
`pads_are_owned_one_use_values_matching_their_committed_copy`); `nonzero(F)`
draw (runtime);
`LinearTerminal.maskingEquiv`, `LinearTerminal.adaptive_uniform_fiber`
(Lean).

**I7. Sumcheck derives equations; it never accepts.** The verifier's output
is `Constraints`, not a decision. Every coefficient is public, every unknown
is a committed cell or an input, and `p_AB` keeps its own coefficient
`r^2` rather than being assumed to equal `p_A*p_B`.
*Enforced by:* `derive_constraints_for_circuits` returns `Constraints`, and
acceptance exists only as `VerifiedProof` from the seal (type, transcript
I10); `LinearTerminal.reduction` (Lean).

**I8. The proof shape is the bound geometry.** The verifier parses the
sumcheck proof against the `SumcheckProofGeometry` derived from the bound
circuits, so a proof with another layer count or round count does not parse.
*Enforced by:* `SumcheckProof::read` is crate-private and called only by the
complete readers, with the sumcheck part of their bound geometry (type,
proto I2); `SumcheckProof::validate` against the schedule's geometry
(runtime).

## Protocol

### Stage arithmetic

At stage `s` the weights `a` (length `nv_s`) are the carried
`a_next` of stage `s-1` followed by the entering output weights; the
assertion coefficients `rho` are this stage's draws. Both roles compute the
public constant before the rounds (`fragments::constant`):

```text
K_a = sum_g a[g] * K[g]                      ; constant streams
C   = claim_s - K_a                          ; claim_0 = 0
```

The prover binds `g,r` (`quad::bind_r_into`), with each assertion's term
using `rho` in place of `a[g]*constants[k]`:

```text
q_l[l] = sum_g a[g] * (sum_r Q[g,l,r]*W[r] + L[g,l]),   C = sum_l q_l[l]*W[l].
```

Tables hold multilinear monomial coefficients; binding the low variable at
`z` maps a pair `(a, b)` to `a + z*b` (`dense::bind`). Round `j`:

```text
p(x) = sum_i (q_l[2i] + x*q_l[2i+1]) * (W[2i] + x*W[2i+1]) = c0 + c1*x + c2*x^2
C    = c0 + c2
C'   = z^2*C + (1-z^2)*c0 + z*c1
```

After `logw_s` rounds at `u = (z_0, ..)`, with `m(u)[i] = prod_j u_j^(bit j of i)`
(`monomial::weights`):

```text
A      = sum_l m(u)[l]*W[l]
B      = sum_l m(u)[l]*q_l[l] = sum_r q_r[r]*W[r] + L(u)
q_r[r] = sum_{g,l} a[g]*Q[g,l,r]*m(u)[l]        ; quad::bind_l_into, both roles
L(u)   = sum_{g,l} a[g]*L[g,l]*m(u)[l]          ; quad::affine_linear
```

The terminal and combine (`fragments::transition`, `symbolic.rs`):

```text
d          = A*p_B + B*p_A - p_D                 ; sent, then r != 0
m_A, m_B   = A + r*p_A, B + r*p_B                ; sent, then alpha
row_s      : C_u + r*(d + p_D) + r^2*p_AB - m_A*m_B = 0     ; C_u: C after the last round
a_next     = m(u) + alpha*q_r
claim_s+1  = m_A + alpha*m_B - r*p_A - alpha*r*p_B - alpha*L(u)
```

After the last stage the zero-layer input weights are added to `a_next`, and
the input equation is `claim_L - sum_i a_next[i]*W[i] = 0`.

### Messages and draws

Per stage `s`, in order. `F` is the participant's field; `e_s` is the number
of entering outputs, `aq_s` and `al_s` the quadratic and linear assertion
counts of the active fragments, `z_in` the sum of `ninput_c` over zero-layer
circuits.

| Step | Prover sends (tag) | Values | Then draws |
|---|---|---|---|
| entry (`s = 0`) | none | | top weights: `e_0 + aq_0 + al_0` elements, from the boundary before the frontend |
| round `j < logw_s` | `SumcheckRound` (48) | Elements(F, 2): `c0-s0`, `c1-s1` | `z_j`: `element(F)` |
| cross | `SumcheckCross` (49) | Elements(F, 1): `d` | `r`: `nonzero(F)` |
| claims | `SumcheckClaims` (50) | Elements(F, 2): `m_A`, `m_B` | `alpha`: `element(F)`; then, if `s+1 < L`, `elements(F, e_{s+1} + aq_{s+1} + al_{s+1})`; if `s+1 = L` and `z_in > 0`, `elements(F, z_in)` |

Weight draws are ordered: entering outputs in global output order, then the
quadratic assertion records of every active fragment in fragment order, then
the linear ones; input weights per zero-layer circuit in statement order,
each added to `omega[0..ninput_c]`.

Per stage: `logw_s + 2` messages, `2*logw_s + 3` elements and `logw_s + 2`
boundaries. A run has `sum_s logw_s + 2L` boundaries, which is the sumcheck
part of the transcript boundary count. A stage with `nw_s = 1` has no rounds
and starts with `SumcheckCross`. A schedule with `L = 0` sends nothing and
draws nothing: its top weights are the zero-layer input weights.

The caller continues the same stream after the last draw. For the prime
participant the split's `eta != 0` follows the input weights in the last
`SumcheckClaims` node (transcript schedule).

### Verifier checks

| Check | Where |
|---|---|
| Top weights come from the current boundary | drawn on entry (`Schedule::draw_top`) |
| Proof has `L` layers with `logw_s` rounds each | `SumcheckProof::read` against the bound geometry; `SumcheckProof::validate` against the schedule |
| Every stage row and the input equation hold | Polygero, after `constraint_compiler` substitutes `x` and the virtual definitions and maps pads to committed coordinates |

The verifier computes `z`, `r`, `alpha`, the weights, `K_a`, `L(u)` and
`q_r` itself. It needs no witness value.

## Formats

### Proof bytes

The sumcheck part of the proof body has no lengths or tags. The geometry
fixes its size: `sum_s (2*logw_s + 3) * F::serialized_size_bytes()`.

```text
sumcheck  := layer{L}                      ; stages from outputs toward inputs
layer     := round{logw_s} cross claims
round     := elem elem                     ; c0 - s0, c1 - s1
cross     := elem                          ; d
claims    := elem elem                     ; m_A, m_B
elem      := canonical serialization of one element of F
```

### Transcript messages

Each message is one tag and one Elements value (transcript I5, I6):

```text
SumcheckRound  := u64(48) u64(2) u64(field_id) u64(2) elem elem
SumcheckCross  := u64(49) u64(2) u64(field_id) u64(1) elem
SumcheckClaims := u64(50) u64(2) u64(field_id) u64(2) elem elem
```

### Committed pad layout

`SumcheckProofGeometry::pad_layout(base)` places the cells after the
participant's private inputs, stage by stage; `pad_count(logw) = 2*logw + 4`
per stage:

| Offset in stage | Cell | `Pad` |
|---|---|---|
| `2j`, `2j+1` for `j < logw_s` | `s0`, `s1` of round `j` | `Round { layer, round, slot }` |
| `2*logw_s` | `p_A` | `Claim { layer, slot: 0 }` |
| `2*logw_s + 1` | `p_B` | `Claim { layer, slot: 1 }` |
| `2*logw_s + 2` | `p_AB = p_A*p_B` | `Product { layer }` |
| `2*logw_s + 3` | `p_D` | `Cross { layer }` |

`sample_pads` returns the cells in exactly this order.

## Rust API

```rust
// runtime::v2::sumcheck, shared by both roles
pub(super) struct Schedule { pub geometry: SumcheckProofGeometry, .. }  // stage layouts and fragment ranges
pub(crate) fn circuit_geometry(circuits: &[&Circuit<F>])
    -> Result<SumcheckProofGeometry, String>;  // the layout only, for participant setup

// prover feature
pub(crate) struct SumcheckPads<const W: usize, F: SerializableField>(..); // not Clone
pub(crate) fn sample_pads<const W: usize, F, R: PrivateRandom>(
    geometry: &SumcheckProofGeometry, rng: &mut R, f: &F,
) -> (SumcheckPads<W, F>, Vec<F::E>);       // cells in pad-layout order
pub(crate) fn evaluate_and_prove_circuits<const W: usize, F>(
    circuits: &[&Circuit<F>],                // I1: from the frontend's Bound
    inputs: Vec<F::E>,                       // [public | private | virtual]
    pads: SumcheckPads<W, F>,                // I6: consumed
    t: &mut TranscriptRef<'_>,                // I1: top weights drawn on entry
    f: &F,
) -> Result<(SumcheckProof<W, F>, Constraints<F::E>), String>;

// verifier feature
pub(crate) fn derive_constraints_for_circuits<const W: usize, F>(
    circuits: &[&Circuit<F>],
    proof: &SumcheckProof<W, F>,             // I8: parsed against the bound geometry
    t: &mut TranscriptRef<'_>,                // I1: top weights drawn on entry
    f: &F,
) -> Result<Constraints<F::E>, String>;      // I7: equations, not a verdict

// runtime::v2::proto::sumcheck, the prover/verifier contract
pub struct SumcheckProof<const W: usize, F> { pub layers: Vec<LayerProof<W, F>> }
pub struct LayerProof<const W: usize, F> {
    pub rounds: Vec<RoundPoly<W, F>>, pub cross: F::E, pub claims: [F::E; 2],
}
impl<const W: usize, F> SumcheckProof<W, F> {
    pub fn geometry(&self) -> std::io::Result<SumcheckProofGeometry>;
    pub fn validate(&self, geometry: &SumcheckProofGeometry) -> std::io::Result<()>;
    pub(crate) fn read(bytes: &mut &[u8], geometry: &SumcheckProofGeometry, f: &F)
        -> std::io::Result<Self>;            // only the complete readers call it (proto I2)
    pub fn write_to_buf(&self, bytes: &mut Vec<u8>, geometry: &SumcheckProofGeometry, f: &F)
        -> std::io::Result<()>;
}
// round counts: core::proto::{MAX_LOGW, sane_logw}, shared with v1
```

The zk frontends call these entry points: `zk::prove`, `zk::prove_split`,
`zk::reduce` and `zk::reduce_split` pass the circuits of their bound part.
Both `evaluate_and_prove_circuits` and `derive_constraints_for_circuits`
build the schedule, validate their inputs against it and then draw the top
weights (`Schedule::draw_top`) before the first message; the prover then
evaluates the circuits. The schedule lives for the call only: it is derived
from the circuits, so the statement does not hold it, and it is not alive
during the commitment and the other sub-protocols around the sumcheck.
`circuit_geometry` computes the layout alone, for participant setup and the
proof reader; it classifies nothing. Each role then runs its own stage loop
(I2): the prover computes each stage's messages from `W` and the pads, the
verifier takes them from the proof, and both loops send and draw only
through the shared steps of `sumcheck/transcript.rs` and the shared
`Schedule` methods. The prover's
internals (`dense`, `eval`, `bind_r_into`) are under `cfg_prover!`; the
verifier loop is under `cfg_verifier!`; the schedule, `symbolic`,
`bind_l_into`, `affine_*`, `monomial` and the message types are shared.
`Constraints`, `PadExpression` and `Pad` stay `pub(crate)`: only the
constraint compiler consumes them.

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Drawing the top weights before the instance is fixed (for the host, before `P256AdapterQuotients` defines the virtual leaves) | I1: the entry point draws them, and the virtual leaves are an argument of the zk frontend call that runs it |
| Top weights drawn for another schedule | I1: the entry point draws them from the schedule it builds |
| Absorbing circuit IDs, depths, public inputs or a constant zero output in sumcheck | I1: sumcheck has no setup message type and no parameter for those values |
| A stage whose weights are drawn with no prover message before them | I2: stage weights follow `SumcheckClaims` of the previous stage; stage 0 weights follow the message before the frontend |
| The cross message chosen after `r`, or the claims after `alpha` | I2: the shared transcript steps send before they draw |
| `r = 0`, which unmasks both claims | I6: `nonzero(F)` |
| Prover and verifier disagreeing on circuit order or fragment offsets | I3: one `Schedule` from the bound statement |
| A zero output weight erasing an assertion | I4: the assertion coefficient replaces the whole weighted coefficient |
| A shorter circuit's false output hidden by the deeper circuit's weights | I4: fresh weights at the entering stage |
| The hash circuit reading R, adapter pads or virtual leaves | I5: prefix ranges |
| Reusing pads across two runs, or passing a proof as pads | I6: `SumcheckPads` is its own move-only type |
| Treating `p_AB` as a checked product | I7: the row keeps `r^2*p_AB`; soundness does not assume honesty |
| Accepting on sumcheck alone, without Polygero | I7: `derive_constraints_for_circuits` returns only `Constraints` |
| Parsing the proof with a different round count | I8: the complete readers parse against the bound geometry |

## Soundness and zero knowledge

**Soundness.** Each challenge has one job; the Lean bound for each is local
and counts roots:

| Challenge | Bad event | Local bound | Lean |
|---|---|---|---|
| `z` (round) | a false `C` becomes true at `z` | 2 roots | `SumcheckV2.bad_round_roots`, `challenge_bad_card_le` |
| `r` (terminal) | `C != A*B` but the row holds | 2 roots among `|F|-1` nonzero values | `LinearTerminal.Data.bad_nonzero_roots`, `LinearTerminal.reduction` |
| `alpha` (combine) | `(m_A, m_B)` unmask to a wrong pair with correct `A + alpha*B` | 1 root | `bad_combine_roots`, `layer_reduction` |
| output and assertion weights | a nonzero output or assertion value cancels | 1 root per answer for the last nonzero slot | `LfzkV2.assertion_reduction`, `AssertionBad` |

`r` and `alpha` cannot be merged: the row is quadratic in `r` only because
`d` is fixed before `r`, and the combine is sound only because `m_A, m_B` are
fixed before `alpha`. The next stage's weights share the answer that holds
`alpha`. The witness and both claims are fixed before that answer, and the
next stage's claim error is affine in `alpha` and the new weights jointly, so
a false pair or a false assertion survives on at most one affine hyperplane
of that answer. Lean tests an answer that carries a combine coordinate and the
next weight coordinates as one affine cancellation, reporting the combine
failure only when every check after it in that answer passes
(`FrontendReplay.combineTest`, `FrontendReplay.layer_combine_cover`), and
charges any one answer at most `2/(|F|-1)`
(`FrontendReplay.QueryTest.bad_card_mul_le`). `Chained.failure_bound` is
the ordinary-round result: for rounds sampled over all of `F` it lifts
per-answer bounds to `2Q/|F| + (Q+1)/|Link|` over an adaptive query tree.
It does not model the terminal challenge, sampled over nonzero `F`. For the
current schedule the application's oracle charging (`ApplicationCharging`,
at the rate `Soundness.Rate7.rate = 2/(q-1)`) lifts the `2/(|F|-1)`
per-answer bound and keeps its denominator. The complete mdoc bound
(`Mdoc.Soundness.averaged_linear_ratio_le`) is
`2Q/(2^128-1) + (choose(Q,2) + R + 15)/2^256`, where `R` is the boundary
count and GF(2^128), the smaller field, sets the leading term. Completeness is
`layer_completeness`, `affine_layer_completeness` and
`LinearTerminal.completeness`; `PadExpression.eval_rounds` and
`LinearTerminal.eval_row`/`eval_nextClaim` show the symbolic equations equal
the numerical ones. `LfzkV2.Current.FrontendReplay` and `FrontendVerifier`
reconstruct the composed constraints from layered topology and carried
fragment weights; `FrontendFailures.accepted_failure_cover` derives a failing
test from an accepted false frontend.

**Zero knowledge.** Each round message is its coefficient minus a fresh
uniform pad, so it is uniform and independent of the witness. For `r != 0`
the map `(p_A, p_B, p_D) -> (d, m_A, m_B)` is a bijection
(`LinearTerminal.maskingEquiv`, `recover_honest`, `honest_recover`), also
when `r` depends adaptively on earlier messages
(`LinearTerminal.adaptive_uniform_fiber`); `p_AB` is derived, not sampled
(`honestPadCells`). The derived equations have public coefficients only; the
committed cells they constrain are hidden by Polygero. The joint statement is
`Mdoc.ZeroKnowledge.statClose`, with distance
`(Q_pre + Q_post)/2^256`, using one joint frontend and backend coin bijection
(`StrandCanonicalExactSimulation.ghost_sameDistribution`).

## Open questions

1. **Schedules with no layers.** A participant whose circuits all have zero
   layers sends no sumcheck message; its top weights are the input weights.
   No mdoc participant has this shape. Recommendation: keep it, because it
   needs no special code (`Schedule::draw_top` draws the input weights), and Lean models it
   (`Frontend.roles` with no stages); state in the transcript design that a
   sub-protocol with no draws may also send nothing.
