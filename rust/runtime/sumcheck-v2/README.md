# Sumcheck V2

`runtime::sumcheck_v2` implements only single-hand sumcheck. The original
`runtime::sumcheck_v1` module implements the legacy two-hand protocol. Import the
module for the desired entry point; there is no protocol selector or proof enum.
Each runtime has its own copies of the sumcheck arithmetic and transcript code.
Both use the shared field, circuit, and randomness modules.

V2 consumes [LFC3](../../core/proto/LFC3.md): three concrete streams per layer,
with no One wire. The v2 compiler, compressor and reader build these streams
directly. LFA2 remains the archive container; temporary experimental payloads are unsupported.

Before witness evaluation, the prover builds all private `split::SplitLayer`
values once. Evaluation traverses their eleven streams explicitly, then sumcheck
consumes the same values and releases each after proving its layer. The reduction
builds each split once as it reaches that layer. Each split borrows the source
token arrays and partitions stored segment records into eleven working streams.
It classifies only coefficient indices 0, 1, 2 and other,
adjusting coordinate deltas and retaining each source segment's full advance.
Class records are contiguous, with a range per source segment; there is no
hashing, deduplication or token rewriting. Both bindings and the linear/constant
corrections use this working layer. The original circuit is
read-only, and the type is not exposed outside `sumcheck_v2`.

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

V2 uses `LayerProof.rounds` and two final claims with their pads subtracted.
Legacy retains its two `hp` vectors. V2 proof
geometry and committed-pad positions belong to `runtime::proto::sumcheck_v2`.
Zero-knowledge proving uses `runtime::zk_v2`; see its [README](../zk-v2/README.md).

## Single-hand transition

The index `g` ranges over this layer's outputs; `l,r` range over its input
wires. The code array `w` holds the input witness `W[i]`, and `V[g]` is the
layer output. In a folding loop, `n` counts the remaining array entries, while
`logw` counts the original Boolean variables. Each fold replaces `n` by
`ceil(n/2)`. All sums are explicit:

$$
V[g] = \sum_l \sum_r \mathrm{QUAD}[g,l,r]\,W[l]\,W[r].
$$

The array `a` contains the current weights on output index `g`. Initially
these are monomial weights at a transcript point; later they are the combined
weights carried from the preceding sumcheck. The incoming claim is

$$
c = \sum_g a[g]\,V[g].
$$

The prover binds `g,r`, leaving `l` free. The code calls this array `q_l`:

$$
q_l[l] = \sum_g \sum_r a[g]\,\mathrm{QUAD}[g,l,r]\,W[r],
\qquad c = \sum_l q_l[l]\,W[l].
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
q_r[r] = \sum_g \sum_l a[g]\,\mathrm{QUAD}[g,l,r]\,m_l[l],
\qquad B = \sum_r q_r[r]\,W[r].
$$

Both bindings live in `quad.rs`. The shared `bind_l` routine performs the public
binding for both roles; `bind_r` consumes witness values and is prover-gated.
Neither routine has an input selector, and neither role imports the other's implementation.

Binding `g,l` lets the verifier express `B` as a claim about `W` without
knowing its values. After absorbing the masked final claims, both sides sample
$\alpha$ and continue with

$$
a_{\mathrm{next}}[i] = m_l[i] + \alpha\,q_r[i],
\qquad c_{\mathrm{next}} = A + \alpha B.
$$

The index `i` labels the same input wires as `l,r`, now viewed as outputs of
the next layer. The terminal sumcheck equation checks that the reduced claim
equals $AB$. Both roles reuse the monomial-weight array as the next `a`, applying
`blas::axpy` directly for the combination.

The formulas above describe ordinary quads. Each assertion marker instead
replaces its entire $a[g]\,\mathrm{QUAD}[g,l,r]$ coefficient by an independent
challenge, sampled in quad traversal order. Both bindings reuse those challenges,
even when several assertion quads share an output index. No bitmap is needed.

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
sampled round challenges in `point_l` and the final-claim combination challenge
`alpha`. The same `point_l` supplies the monomial weights. At the end, the prover
passes these challenges and the final dense input weights to the shared symbolic
builder. Both compute the next claim directly from the round coefficients.

`symbolic::build_constraints` uses the proof messages, sampled challenges, and
final input weights to construct sumcheck constraints. It evaluates round polynomials,
constrains each final product, combines the final claims, and records the input
constraint. Pad terms refer to logical sumcheck positions by layer, round, and
message slot. The final input constraint retains the dense input weights.

`runtime::zk_v2::constraint_compiler` maps these logical pads to committed witness
positions, substitutes public inputs, and emits sparse Polygero entries. Committed
products of final-claim pads lower the terminal quadratic terms to linear rows; the
ZK context fixes the quadratic product-consistency constraints before commitment.
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

The transcript domain is `longfellow-sumcheck-v2-projective`. Assertion sampling
uses a separate domain and layer index; final-claim combination uses its own domain
after the final-claim message. Both roles use `transcript::end_layer` for that
boundary and `quad::weights_next_affine` for the public weight update.
Legacy transcript operations are unchanged.

| Per-layer quantity | Single-hand | Legacy round-major |
|---|---:|---:|
| Round polynomials | `logw` | `2 logw` |
| Transmitted field elements | `2 logw + 2` | `4 logw + 2` |
| Committed pad coordinates | `2 logw + 3` | `4 logw + 3` |

The third final-claim pad coordinate is the product of the first two. Each layer
still has one terminal linear constraint and one pad-product constraint.

## Compiler selection and testing

Both protocols are modules in the `longfellow-zk` crate. The compiler's existing
`compile_v1` entry point preserves historical Morton ordering and circuit IDs.
`compile_v2` uses constant-aware, output-major ordering and targets V2. No wire
IDs change between these layouts. The mdoc NEXT v9 builders, geometry, prover, and
verifier use V2; v5-v7 verification uses the stored legacy circuits.

The shared compiler and circuit suites, including mdoc synthesis and tampering
checks, run with both compiler entry points. Legacy tests retain circuit-ID and
RFC proof-byte fixtures. Runtime tests check independent numerical and symbolic
constraints, independent constraint derivation, proof/transcript fingerprints,
malformed proofs, final-claim pads, arbitrary V2 traversal, zero-round and zero-layer circuits,
and sparse lowering over prime and binary fields.

From `rust/`, run `cargo test --release --features testonly` for the complete
suite. Filter with `v1_tests` or `v2_tests` to run the shared circuit suites
under one compiler, or with `runtime::sumcheck_v1` / `runtime::sumcheck_v2` for the
sumcheck protocols. Both paths use the existing Cargo feature gates.

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
