# Sumcheck NG

`runtime-sumcheck-ng` implements only single-hand sumcheck. The original
`runtime-sumcheck` crate implements the legacy two-hand protocol. Import the
crate for the desired entry point; there is no protocol selector or proof enum.
Each runtime has its own copies of the sumcheck arithmetic and transcript code.
Both use the shared field, circuit, and randomness crates.

## Organization

| Responsibility | Legacy | NG |
|---|---|---|
| Numerical prover | `sumcheck/src/prover.rs` | `sumcheck-ng/src/prover.rs` |
| Local verifier data | — | `sumcheck-ng/src/verifier_data.rs` |
| Pure symbolic verifier | — | `sumcheck-ng/src/symbolic.rs` |
| Ligero constraint compiler | — | `zk-ng/src/constraint_compiler.rs` |
| Numerical verifier and independent data derivation | `sumcheck/src/verifier.rs` | `sumcheck-ng/src/verifier.rs` |
| Wiring contraction | `sumcheck/src/hquad.rs` | `sumcheck-ng/src/wiring.rs` |
| Equality weights | `sumcheck/src/eq.rs` | `sumcheck-ng/src/eq.rs` |
| Circuit evaluation and assertion discovery | `sumcheck/src/eval.rs` | `sumcheck-ng/src/eval.rs` |
| Transcript operations | `sumcheck/src/transcript.rs` | `sumcheck-ng/src/transcript.rs` |
| Proof codec | `proto/src/sumcheck.rs` | `proto/src/sumcheck_ng.rs` |
| ZK proof codec and witness counts | `proto/src/zk.rs` | `proto/src/zk_ng.rs` |

There is no `transition.rs` or strategy submodule. NG uses `LayerProof.rounds`
and two endpoint claims with their pads subtracted. Legacy retains its two `hp` vectors. NG proof
geometry and committed-pad positions belong to `runtime-proto::sumcheck_ng`.
Zero-knowledge proving uses `runtime-zk-ng`; see its [README](../zk-ng/README.md).

## Single-hand transition

The incoming statement is `c = dot(lambda, v)`. For ordinary quadratic terms,
contract the output index using `lambda`. Assertion-marker terms instead get
fresh independent weights, sampled in ascending output-index order at each
layer. The compiler emits one marker product per assertion output; validation
rejects multiple markers at the same output to prevent cancellation.

The prover computes `H = M w` and folds `H` and `w` through `logw` quadratic
rounds. Its two endpoints are `A = W(u)` and `B = H(u)`. The terminal equation
is `t = A B`, with no extra wiring scalar and no division. Both sides compute
`mu = M^T chi(u)`. After absorbing the endpoint messages, they sample `alpha`
and continue with `lambda = chi(u) + alpha mu` and `c = A + alpha B`.

The numerical prover advances the main transcript directly and returns the proof
plus `VerifierData`. For each round, the verifier data retains `L1(r)`,
`L0(r) - L1(r)`, and `L2(r)`; it also retains each layer's endpoint-combination
challenge `alpha` and the final dense input weights. Interpolation coefficients
are computed once and used for both numerical reduction and symbolic constraints.
The final weight vector is moved into the result.

`symbolic::verify` consumes the proof and verifier data and purely constructs
sumcheck acceptance relations. It owns round reduction, terminal endpoint
products, endpoint combination, and the final input equation. Relations refer
to logical sumcheck pads by layer and round; they contain no commitment indices,
Ligero types, transcript, or circuit. The final dense weights move into the input
relation. Only per-round scalar terms and final input weights are retained.

`runtime-zk-ng::constraint_compiler` maps these logical pads to committed witness
positions, substitutes public inputs, and emits sparse Ligero entries. Committed
endpoint-pad products lower the terminal quadratic terms to linear rows; the
compiler also supplies the quadratic product-consistency constraints. Zero
coefficients are omitted, while every constraint row and its constant is kept.
Sumcheck random values are called pads; mask refers to Ligero mask rows.

For verification, `derive_verifier_data` independently samples challenges and
derives coefficients and final weights from the circuit, proof, and transcript.
It validates shape; deriving data alone does not establish acceptance. The same
symbolic verifier constructs relations, whose compiled constraints Ligero checks.
Numerical verification with revealed inputs and pads evaluates those relations
directly. Verifier data and relations are never serialized or accepted from a
proof.

Proving does not repeat assertion discovery or sampling, equality expansion, or
wiring contraction. Ligero continues on the already advanced main transcript,
without a clone, replay, observer, or callback. Intermediate dense vectors live
within their layer, and fold buffers use lexical scopes.

The prover collects assertion-output metadata during circuit evaluation. For
each layer it contracts `M w` once, folds the two work arrays once, expands
`chi(u)` once, and contracts `M^T chi(u)` once. It passes the fully expanded
`chi(u) + alpha mu` array directly into the next layer. Equality tables and dense
coefficient arrays are not cached across all layers.

The transcript domain is `longfellow-sumcheck-single-hand-v1`. Assertion sampling
uses a separate domain and layer index; endpoint combination uses its own domain
after the endpoint message. Legacy transcript operations are unchanged.

| Per-layer quantity | Single-hand | Legacy round-major |
|---|---:|---:|
| Round polynomials | `logw` | `2 logw` |
| Transmitted field elements | `2 logw + 2` | `4 logw + 2` |
| Committed pad coordinates | `2 logw + 3` | `4 logw + 3` |

The third endpoint pad coordinate is the product of the first two. Each layer
still has one terminal linear constraint and one pad-product constraint.

## Legacy comparison and remaining discrepancies

The restoration baseline is local `main`, commit
`bf9eef3` (Merge pull request #213). The available `origin/main` points to
`d9d8d6a`; it was not substituted for local `main`.

All production files under `runtime/sumcheck/src` and `runtime/zk/src`, their
manifests, and the original sumcheck/ZK codec files are byte-for-byte identical
to that local-main baseline. `runtime-proto/src/lib.rs` adds only the two NG
module declarations. Its existing tests are restored; NG codec tests live in
`tests/proto_ng.rs`.

Two legacy test files differ from main: sumcheck's compiler-generated fixtures
and ZK's raw-circuit fixtures explicitly construct Morton traversal. The shared
compiler now emits NG traversal only. Restoring the main tests unchanged exposed
a failing legacy multi-layer test because it consumed that new traversal.
The production legacy prover was kept unchanged.

The compiler is not forked or restored. Its existing type/output-major ordering
and shared `core-proto::compare_term` changes remain on this branch. Existing
core reader support for an opt-in total-term limit also remains; the default
limit is unchanged. Rebuilding historical circuits with this compiler is outside
this split. Legacy mdoc v5-v7 uses its stored circuits; mdoc v8 and MLDSA use NG.
The shared algebra, randomness, Merkle, and Ligero runtime source has no differences
from local main.

## Validation

From `rust/`:

```sh
cargo test --workspace --release
cargo clippy --no-deps -p runtime-sumcheck-ng -p runtime-zk-ng --all-targets -- -D warnings
```

Runtime tests cover legacy RFC proof bytes, independent numerical/symbolic
transcripts, equivalence of prover-produced and independently derived verifier data, malformed NG proof shapes, endpoint pads and their products, assertion independence, arbitrary NG traversal,
zero-width layers, and zero-layer circuits. No new formal soundness proof is
included.

A deterministic compatibility test fixes complete proof bytes and final transcript
state to pre-cleanup fingerprints. It also compares every verifier-data field and
constraint coefficient against independent verifier derivation. See the
[benchmark report](../../experiments/mldsa/SINGLE_HAND_REPORT.md) for release
validation and timing results.

Independent lowering tests compare full numerical interpolation, logical relation
evaluation, and compiled Ligero residuals over prime and binary fields. They cover
multiple layers, zero-round and zero-layer cases, public/private input splits,
zero weights, constant-only constraints, and endpoint-product tampering.
