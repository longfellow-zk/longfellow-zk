# Sumcheck V2

`runtime::sumcheck_v2` implements only single-hand sumcheck. The original
`runtime::sumcheck_v1` module implements the legacy two-hand protocol. Import the
module for the desired entry point; there is no protocol selector or proof enum.
Each runtime has its own copies of the sumcheck arithmetic and transcript code.
Both use shared field and randomness modules; v2 consumes native LFC3 circuits.

## Organization

| Responsibility | Legacy | V2 |
|---|---|---|
| Numerical prover | `sumcheck-v1/src/prover.rs` | `sumcheck-v2/src/prover.rs` |
| Symbolic constraint construction | `sumcheck-v1/src/symbolic.rs` | `sumcheck-v2/src/symbolic.rs` |
| Commitment constraint compiler | `zk-v1/src/constraint_compiler.rs` | `zk-v2/src/constraint_compiler.rs` |
| Constraints from public messages | `sumcheck-v1/src/verifier.rs` | `sumcheck-v2/src/reduction.rs` |
| Revealed-pad verification | `sumcheck-v1/src/verifier.rs` | `sumcheck-v2/src/verifier.rs` |
| Quad binding | `sumcheck-v1/src/hquad.rs` | `sumcheck-v2/src/quad.rs` |
| Multilinear weights | `sumcheck-v1/src/eq.rs` | `sumcheck-v2/src/monomial.rs` |
| Circuit evaluation | `sumcheck-v1/src/eval.rs` | `sumcheck-v2/src/eval.rs` |
| Transcript operations | `sumcheck-v1/src/transcript.rs` | `sumcheck-v2/src/transcript.rs` |
| Proof codec | `proto/src/sumcheck_v1.rs` | `proto/src/sumcheck_v2.rs` |
| ZK proof codec and witness counts | `proto/src/zk_v1.rs` | `proto/src/zk_v2.rs` |

Protocol rounds, pad sampling, and construction of
the two transmitted round coefficients live together in `prover.rs`; no polynomial
adapter traits are needed. Dense binding and scalar extraction live in `dense.rs`.
Ordinary tests live in private modules under `tests/`.
`verifier.rs` is the explicit exception: it verifies with revealed pads
for testing and is not used in production. Production verification uses
`runtime::zk_v2::ZkVerifier` and Polygero.

V2 uses `LayerProof.rounds`, a masked cross coefficient, and two final claims
with independently sampled pads scaled by a fresh nonzero challenge.
Legacy retains its two `hp` vectors. V2 proof
geometry and committed-pad positions belong to `runtime::proto::sumcheck_v2`.
Zero-knowledge proving uses `runtime::zk_v2`; see its [README](../zk-v2/README.md).

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
[LFC3 format](../../core/proto/LFC3.md) for encoding and circuit identity.

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
these are monomial weights at a transcript point; later they are the combined
weights carried from the preceding sumcheck. The incoming claim is

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

Both bindings live in `quad.rs`. The shared `bind_l` routine performs the public
binding for both roles; `bind_r` consumes witness values and is prover-gated.
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

`runtime::zk_v2::constraint_compiler` maps these logical pads to committed witness
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

Each layer samples its assertion challenges once and reuses them in both quad
bindings. The prover forms `q_l` once, folds both arrays once,
expands `m_l[i]` once, and forms `q_r` once. Intermediate arrays
live within their layer; only the final combined input weights survive.
Polygero continues on the advanced main transcript without replay.

The initial output point has exactly `logv` sampled coordinates; a scalar output
consumes none. Each layer then samples exactly `logw` round challenges. The codec
independently caps serialized layers at 40 rounds, regardless of host index width;
runtime circuit execution also checks its index capacity.

The transcript domain is `longfellow-sumcheck-v2-projective-linear-terminal-v1`. Assertion sampling
uses a separate domain and layer index; final-claim combination uses its own domain
after the final-claim message. Both roles use `transcript::end_layer` for that
boundary and `quad::weights_next_affine` for the public weight update.
Legacy transcript operations are unchanged.

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
both final evaluations masked. These local masking facts do not constitute
a complete joint-view zero-knowledge proof.

The [packed Lean composition](../../../formal/lfzk-v2/README.md) targets
`fcf8a3a`, which predates this terminal reduction and still checks pad products.
Its numerical endpoint must be adapted before being applied to this protocol.

## Compiler selection and testing

Both protocols are modules in the `longfellow-zk` crate. The compiler's existing
`compile_v1` entry point preserves historical Morton ordering and circuit IDs.
`compile_v2` lowers directly to LFC3 and removes the reserved One wire. NEXT v9
uses that representation; v5-v7 verification uses the stored legacy circuits.

The circuit synthesis and tampering suites use the native v2 compiler. Dedicated
backend tests pin v1 circuit bytes and compare v1/v2 evaluation over binary and
prime fields. Saved v1 proofs remain byte-for-byte fixtures. Runtime tests check
split and reference execution, affine corrections, independent numerical and
symbolic constraints, proof/transcript agreement, malformed encodings, arbitrary
traversal, zero-round and zero-layer circuits, and sparse constraint lowering.

From `rust/`, run `cargo test --offline --release --features testonly` for the
complete suite. Filter with `runtime::sumcheck_v1` or `runtime::sumcheck_v2` for
one protocol. Both paths use the existing Cargo feature gates.


## Feature boundaries

`prover` enables dense binding, pad sampling, witness evaluation, round-polynomial
construction, and numerical proving. `verifier` enables public constraint
derivation and the revealed-pad diagnostic verifier. The production ZK path uses
the derived constraints through Polygero. Proof codecs, transcript operations,
monomial weights, public tensor binding, and symbolic constraints are shared
runtime code. Compile-time fields and circuit synthesis are used only by tests.

The private prover and verifier modules in `runtime::zk_v2` are separately gated;
their `ZkProver` and `ZkVerifier` entry points are re-exported at the module root.
Both use the same pure constraint compiler and neither imports the other.
The legacy path has the same symbolic-constraint / constraint-compiler abstraction:
`runtime::sumcheck_v1::symbolic` owns the constraints and
`runtime::zk_v1::constraint_compiler` lowers them to Ligero constraints.
