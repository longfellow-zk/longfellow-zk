# Sumcheck V2

`runtime::v2::sumcheck` implements single-hand sumcheck over one or more circuits
using sparse quad fragments. The original
`runtime::v1::sumcheck` module implements the legacy two-hand protocol. Import the
module for the desired entry point; there is no protocol selector or proof enum.
Each runtime has its own copies of the sumcheck arithmetic and transcript code.
Both use shared field and randomness modules; v2 consumes native LFC3 circuits.

## Organization

Paths below are relative to `runtime/`.

| Responsibility | Legacy | V2 |
|---|---|---|
| Shared quad-fragment schedule | — | `v2/sumcheck/src/fragments.rs` |
| Numerical prover | `v1/sumcheck/src/prover.rs` | `v2/sumcheck/src/prover.rs` |
| Symbolic constraint construction | `v1/sumcheck/src/symbolic.rs` | `v2/sumcheck/src/symbolic.rs` |
| Commitment constraint compiler | `v1/zk/src/constraint_compiler.rs` | `v2/zk/src/constraint_compiler.rs` |
| Constraints from public messages | `v1/sumcheck/src/verifier.rs` | `v2/sumcheck/src/verifier.rs` |
| Revealed-pad verification | `v1/sumcheck/src/verifier.rs` | `v2/sumcheck/tests/diagnostic.rs` |
| Quad binding | `v1/sumcheck/src/hquad.rs` | `v2/sumcheck/src/quad.rs` |
| Multilinear weights | `v1/sumcheck/src/eq.rs` | `v2/sumcheck/src/monomial.rs` |
| Circuit evaluation | `v1/sumcheck/src/eval.rs` | `v2/sumcheck/src/eval.rs` |
| Transcript operations | `v1/sumcheck/src/transcript.rs` | `v2/sumcheck/src/transcript.rs` |
| Proof codec | `v1/proto/src/sumcheck.rs` | `v2/proto/src/sumcheck.rs` |
| ZK proof codec and witness counts | `v1/proto/src/zk.rs` | `v2/proto/src/zk.rs` |

Protocol rounds, pad sampling, and construction of
the two transmitted round coefficients live together in `prover.rs`; no polynomial
adapter traits are needed. Dense binding and scalar extraction live in `dense.rs`.
Ordinary tests live in private modules under `tests/`.
`verifier.rs` reconstructs the public constraints; `tests/diagnostic.rs`
evaluates them with revealed pads for tests. Complete verification uses
`runtime::v2::zk::ZkVerifier` and Polygero.

V2 uses `LayerProof.rounds`, a masked cross coefficient, and two final claims
with independently sampled pads scaled by a fresh nonzero challenge.
Legacy retains its two `hp` vectors. V2 proof
geometry and committed-pad positions belong to `runtime::v2::proto::sumcheck`.
Zero-knowledge proving uses `runtime::v2::zk`; see its [README](../zk/README.md).

## Circuit storage and execution

LFC3 stores quadratic, linear, and constant terms in three streams, with an
explicit coefficient table and no reserved One input. Each invocation classifies
the coefficient table once. The private split uses four quadratic streams and
four linear streams (general, one, minus one, and assertions), plus three constant
streams. In characteristic two, minus one shares the one stream.

The split preserves repeated segment runs and borrows their token sequences.
The prover builds it once for witness evaluation and reuses it for sumcheck,
releasing each layer after proving it. The verifier constructs one layer at a time.
Unit-coefficient arithmetic is confined to these eleven streams. See the
[LFC3 format](../../../core/proto/LFC3.md) for encoding and circuit identity.

## Quad fragments and global layer arrays

A `QuadFragment` identifies one supplied circuit's sparse terms at a layer,
including its quadratic, linear and constant streams. Its ranges translate
local gate indices into the global arrays. A `SplitFragment` adds the eleven-way
split and sampled assertion coefficients. Neither owns a wire array.

All circuits read one shared input array and share its public prefix. A circuit
may declare fewer inputs than another: the array is as wide as the widest
circuit, and each circuit reads the prefix given by its own `ninput`. A circuit
therefore cannot address inputs beyond its declared width, which lets an
application place values that one circuit must never read after that circuit's
inputs. Every intermediate layer is the contiguous concatenation of its active
circuits' wires. Local wire indices start at zero; their offset is the sum of
the preceding circuits' widths. There is no padding between circuits. At the
common input boundary every circuit's input offset is zero.

For example, three intermediate widths 3, 5 and 3 occupy ranges `0..3`, `3..8`
and `8..11`. Sumcheck uses `ceil(log2(11))` wire rounds. Missing coefficients
beyond the end of the entire array are implicitly zero, as for an ordinary
single circuit. Circuit indices introduce no extra protocol coordinates,
terminal claims or combination challenges.

A layer has one witness array W, one bound coefficient array q_l and one round
polynomial. Sparse tensor binding iterates over quad fragments using
slices at their offsets; dense folding operates on the global arrays. The
verifier similarly constructs one monomial array and one q_r, then applies the
ordinary `m(u) + alpha*q_r` transition once with `blas::axpy`. Circuits do not
receive separate witness or claim arrays. Their only separate state is sparse
circuit metadata and independently sampled assertion coefficients.

Circuits align at their inputs. A depth-three circuit joins a depth-five
circuit at stage two, adding freshly weighted zero outputs to the current
claim. Each output receives an independent field weight, including scalar
outputs. Evaluation checks all circuit outputs and assertions; once a
circuit finishes, its checked zero outputs leave the global witness array.
A zero-layer circuit asserts that its input prefix vanishes and joins the
final input claim directly.

The ZK layer commits the common inputs once, runs this ordinary sumcheck and
performs one packing reduction. Binary sources remain Boolean and degree-one
packing remains a no-op. Circuits must agree on the public prefix and each
circuit's input layer must span exactly its declared width.

## Single-hand transition


The index `g` ranges over this layer's outputs; `l,r` range over its input
wires. The code array `w` holds the input witness `W[i]`, and `V[g]` is the
layer output. In a folding loop, `n` counts the remaining array entries, while
`logw` counts the original Boolean variables. Each fold replaces `n` by
`ceil(n/2)`. All sums are explicit:

$$
V[g] = \sum_{l,r} Q[g,l,r]W[l]W[r] + \sum_l L[g,l]W[l] + K[g].
$$

The array `a` contains the current weights on output index `g`. Initially
these are independent weights on outputs as circuits enter; later they are
the combined weights carried from the preceding sumcheck. The incoming claim is

$$
c = \sum_g a[g]\,V[g].
$$

The prover binds `g,r`, leaving `l` free. The code calls this array `q_l`:

$$
q_l[l] = \sum_g a[g]\left(\sum_r Q[g,l,r]W[r] + L[g,l]\right),
\qquad c - \sum_g a[g]K[g] = \sum_l q_l[l]W[l].
$$

Sumcheck binds the bits of `l` at challenges collected in `point_l = u`.
The array `m_l[i]` contains $\prod_j u_j^{i_j}$, where $i_j$ is bit $j$ of $i$.
The unmasked final claims are

$$
A = \sum_l m_l[l]\,W[l] = W(u),
\qquad B = \sum_l m_l[l]\,q_l[l].
$$

Both prover and verifier bind `g,l`, leaving `r` free. The code calls this
array `q_r`:

$$
q_r[r] = \sum_{g,l} a[g]Q[g,l,r]m_l[l],
\qquad B = \sum_r q_r[r]W[r] + L(u),\quad L(u)=\sum_{g,l}a[g]L[g,l]m_l[l].
$$

Both bindings live in `quad.rs`. The shared `bind_l_into` routine accumulates public
bindings into the global q_r for both roles; `bind_r_into` consumes witness
values and accumulates q_l only in the prover.
Neither routine has an input selector, and neither role imports the other's implementation.

Binding `g,l` lets the verifier express `B` as a claim about `W` without
knowing its values. After absorbing the masked final claims, both sides sample
$\alpha$ and continue with

$$
a_{\mathrm{next}}[i] = m_l[i] + \alpha\,q_r[i],
\qquad c_{\mathrm{next}} = A + \alpha(B-L(u)).
$$

The index `i` labels the same input wires as `l,r`, now viewed as outputs of
the next layer. The terminal sumcheck equation checks that the reduced claim
equals $AB$. Both roles reuse the monomial-weight array as the next `a`, applying
`blas::axpy` directly for the combination.

Each quadratic or linear assertion replaces its entire output-weighted
coefficient by an independent challenge, sampled in quadratic then linear
traversal order. Both bindings reuse those challenges, even when several
assertions share an output index. Linear assertions also enter the public
$L(u)$ correction. No bitmap is needed.

V2 treats each table as multilinear monomial coefficients, equivalently values on
the projective cube $\{0,\infty\}^{\mathrm{logw}}$. Binding a pair uses
$a+zb$. For each round,

$$
p(x)=c_0+c_1x+c_2x^2,\qquad C=c_0+c_2,
\qquad C'=z^2C+(1-z^2)c_0+zc_1.
$$

The messages contain masked $c_0,c_1$. No Lagrange basis or third interpolation
point is needed. This projective formulation follows Dao, Biswas, Eagen, Milson,
Papini, and Thaler, [*The Sum-Check Protocol over the Monomial Basis, and Other
Optimizations*](https://eprint.iacr.org/2026/762).
The v2 transcript domain distinguishes this protocol from the earlier affine
binding; previously generated v2 proofs require their original verifier.

The numerical prover advances the main transcript directly and returns the proof
and its symbolic constraints. During proving, each `LayerChallenges` retains the
sampled round challenges in `point_l`, the nonzero terminal challenge, and
the final-claim combination challenge `alpha`, together with the public constant and linear corrections. The same `point_l` supplies the monomial weights. At the end, the prover
passes these challenges and the final dense input weights to the shared symbolic
builder. Both compute the next claim directly from the round coefficients.

`symbolic::build_constraints` uses the proof messages, sampled challenges, and
final input weights to construct sumcheck constraints. It evaluates round polynomials,
constrains each final product, combines the final claims, and records the input
constraint. Pad terms refer to logical sumcheck positions by layer, round, and
message slot. The final input constraint retains the dense input weights.

`runtime::v2::zk::constraint_compiler` maps these logical pads to committed witness
positions, substitutes public inputs, and emits sparse Polygero entries. Committed
terminal cells enter affine rows; a fresh terminal challenge supplies the
product check described below. Polygero enforces only linear constraints.
Every coefficient is retained, including zeros, along with each constraint's constant.
Sumcheck random values are called pads; mask refers to Polygero mask rows.

For verification, `derive_constraints` independently samples challenges and
derives final input weights from the circuit, proof, and transcript. It validates
the proof's shape, calls the same symbolic builder, and returns constraints ready
for the ZK compiler. Polygero checks the compiled constraints.
Numerical verification with revealed inputs and pads evaluates those constraints
directly. Both parties reconstruct the challenges, input weights, and constraints
from the circuit and transcript.

One layer answer supplies every fragment's assertion coefficients, which are
reused in both quad bindings. Across a complete layer the prover forms `q_l` once, folds both
arrays once, expands `m_l[i]` once, and forms `q_r` once. Intermediate arrays
live within their layer; only the final combined input weights survive.
Polygero continues on the advanced main transcript without replay.

Each entering circuit samples one weight per output; each global layer then
samples exactly `ceil(log2(nw))` round challenges. The codec independently caps
serialized layers at 40 rounds, regardless of host index width; circuit
execution also checks its index capacity.

The transcript binds the ordered circuit list and depths under
`layered-sumcheck/circuits/v1`: each circuit contributes its ID and depth. The
mdoc binary participant combines its archived hash circuit with the fixed
adapter fragment, whose leaves are per-proof virtual inputs rather than
circuit coefficients. Entering circuit outputs and explicit assertions
share the same assertion answer. `transcript::end_layer` binds the two final claims before the
ordinary alpha challenge. Prover and verifier share the fragment layout and
public transition arithmetic; legacy transcript operations are unchanged.

| Per-layer quantity | Single-hand | Legacy round-major |
|---|---:|---:|
| Round polynomials | `logw` | `2 logw` |
| Transmitted field elements | `2 logw + 3` | `4 logw + 2` |
| Committed pad coordinates | `2 logw + 4` | `4 logw + 3` |

The terminal cells are `p_A,p_B,p_AB,p_D`. The honest prover sets
`p_AB=p_A*p_B` and samples the other three independently before commitment.
Each layer contributes one affine terminal equation; there are no backend
multiplication constraints.

Before sending the final claims, the prover sends

```text
d = A*p_B + B*p_A - p_D.
```

After binding `d`, both sides sample a fresh nonzero `r`. The prover sends
`m_A=A+r*p_A` and `m_B=B+r*p_B`; only then is `alpha` sampled. The terminal
and next-layer equations become

```text
C + r*(d+p_D) + r^2*p_AB - m_A*m_B = 0,
claim_next = m_A + alpha*m_B - r*p_A - alpha*r*p_B - alpha*L(u).
```

Both equations are affine in the committed values. To see why a dishonest
`p_AB` does not bypass soundness, fix a decoded witness and its genuine terminal
evaluations `A,B` before `r`. Expanding the terminal error gives

```text
(C-A*B) + r*(d+p_D-A*p_B-B*p_A) + r^2*(p_AB-p_A*p_B).
```

If `C != A*B`, this polynomial is nonzero and has at most two nonzero roots,
so this step contributes at most `2/(|F|-1)` in the ideal uniform-challenge
model. A claimed pair different from the genuine evaluations is handled by
the following combination challenge and layer reduction. The cross message
must precede `r`; allowing it to depend on `r` would defeat this argument.
The independent `p_D` masks the cross coefficient, and excluding zero keeps
both final evaluations masked. The complete mdoc zero-knowledge proof composes
these masking laws with the shared commitment and the other frontend/backend
coin changes, preserving their joint view.

The [current Lean composition](../../../../formal/lfzk-v2/README.md) models
quad-fragment traversal, shared inputs and circuits entering at different depths,
including scalar outputs and zero-layer circuits. It connects the final input
claim to authenticated packing and the joint commitment, including the MAC-free
mdoc adapter and early witness selection. Its current rate-1/7 soundness analysis
gives the exact saturated bound for `Q < 2^127` and a convenient approximation
for every distinct-query budget `Q >= 0`, as stated in the formal README.
The joint-view zero-knowledge theorem retains complete proofs, failure outcomes
and observer query traces. Trusted circuit/arithmetic setup and the ideal-oracle
and sampling assumptions remain explicit; Rust correspondence is source-audited.

## Compiler selection and testing

Both protocols are modules in the `longfellow-zk` crate. The compiler's existing
`compile_v1` entry point preserves historical Morton ordering and circuit IDs.
`compile_v2` lowers directly to LFC3 and removes the reserved One wire. NEXT v12
uses that representation; v5-v7 verification uses the stored legacy circuits.

The circuit synthesis and tampering suites use the native v2 compiler. Dedicated
backend tests pin v1 circuit bytes and compare v1/v2 evaluation over binary and
prime fields. Saved v1 proofs remain byte-for-byte fixtures. Runtime tests check
split and reference execution, affine corrections, independent numerical and
symbolic constraints, proof/transcript agreement, malformed encodings, arbitrary
traversal, quad fragments versus physically merged circuits, shared inputs, unequal
depths and widths, zero-round and zero-layer circuits, and sparse constraint lowering.

From `rust/`, run `cargo test --offline --release --features testonly` for the
complete suite. Filter with `runtime::v1::sumcheck` or `runtime::v2::sumcheck` for
one protocol. Both paths use the existing Cargo feature gates.


## Feature boundaries

`prover` enables dense binding, pad sampling, witness evaluation, round-polynomial
construction, and numerical proving. `verifier` enables public constraint
derivation; the revealed-pad diagnostic verifier is compiled only for tests.
The production ZK path uses
the derived constraints through Polygero. Proof codecs, transcript operations,
monomial weights, public tensor binding, and symbolic constraints are shared
runtime code. Compile-time fields and circuit synthesis are used only by tests.

The private prover and verifier modules in `runtime::v2::zk` are separately gated;
their `ZkProver` and `ZkVerifier` entry points are re-exported at the module root.
Both use the same pure constraint compiler and neither imports the other.
The legacy path has the same symbolic-constraint / constraint-compiler abstraction:
`runtime::v1::sumcheck::symbolic` owns the constraints and
`runtime::v1::zk::constraint_compiler` lowers them to Ligero constraints.
