# Single-hand sumcheck integration

2026-10-21. Single-hand replaces experimental hand-major. The original
round-major protocol remains available for historical mdoc v5–v7 and C++/RFC
compatibility. See the [protocol organization](../../runtime/sumcheck-ng/README.md)
for the implementation boundaries and transition equations.

## Current crate split

Single-hand now lives in `runtime-sumcheck-ng` and `runtime-zk-ng`, with codecs
in `runtime-proto::sumcheck_ng` and `runtime-proto::zk_ng`. The legacy sumcheck/ZK
production sources and codec files are restored from local main (`bf9eef3`).
The compiler stays shared and produces NG circuits only. The NG implementation
has no strategy selectors or observer callbacks.
The [NG README](../../runtime/sumcheck-ng/README.md) records exact restoration
boundaries and the two legacy test fixture adaptations needed for Morton order.
The historical timing sections below predate this crate split.

## Symbolic verifier and constraint compiler

Sumcheck-ng now owns both verifier preprocessing and pure acceptance algebra.
`derive_verifier_data` independently derives `VerifierData` from the circuit,
proof, and transcript. The numerical prover produces the same data without
repeating its protocol work. `symbolic::verify` consumes that data and constructs
relations for round reduction, endpoint products and combination, and final input
binding. It has no transcript, circuit, Ligero types, or commitment coordinates.
The final dense input weights move into the input relation.

ZK-ng's `constraint_compiler` maps logical sumcheck pads to committed witness
positions, substitutes public inputs, and lowers endpoint-pad products to their
committed product slots and quadratic consistency constraints. It emits sparse
entries, skips zero coefficients, and preserves rows and constants. Pad denotes
sumcheck random values; mask is reserved for Ligero mask rows. The old ZK
symbolic-verifier module and its physical-coordinate expression helper are gone.

Numerical verification evaluates the same logical relations with revealed pads
and inputs. Independent tests compare those residuals and compiled Ligero rows
against a separate numerical recurrence using full three-point interpolation.
Coverage includes prime and binary fields, zero-round and zero-layer circuits,
public/private splits, zero coefficients, constant-only constraints, malformed
local data, and endpoint-product tampering. The existing proof-byte and
transcript fingerprints remain unchanged.

## Checkpoint validation and benchmarks

The final `cargo test --workspace --release` run passed 557 tests, with zero
failures and 23 offline/benchmark tests ignored by default. Strict Clippy passes
for both NG crates and all their targets with `-D warnings`. Proof-byte and final
transcript fingerprints are unchanged. Legacy production sources and codecs
still match local main (`bf9eef3`); the existing fixture exceptions are documented
in the [NG README](../../runtime/sumcheck-ng/README.md).

Fresh release/native binaries ran sequentially on CPU 2, boost disabled, allocation
tracking disabled for timing. v8 uses the same two-attribute archive, one warmup,
and five measured runs; its values are medians. MLDSA has one fresh-process run
per variant with unchanged default circuit policy and circuit IDs. All proofs
were serialized, parsed, and verified.

| Workload | Commit ms | Prove ms | Verify ms | Proof bytes |
|---|---:|---:|---:|---:|
| v8 full application flow | included | 279.709 | 142.112 | 308900 |
| MLDSA-44 | 287.504 | 798.431 | 625.124 | 200900 |
| MLDSA-65 | 330.233 | 942.558 | 742.075 | 211292 |

v8 full flow includes commitment, circuit loading, witness preparation, and
serialization. MLDSA prove excludes commitment, circuit compilation/loading, and
serialization. Proof sizes are unchanged.

A separate v8 allocation-tracking binary measured one full flow, no warmup,
with `V8_COMPONENTS=flow`. Peak additional heap was 92,263,666
bytes (87.99 MiB) for proving and
50,274,304 bytes (47.95 MiB)
for verification, relative to each operation's live-heap baseline. `/usr/bin/time
-v` measured 104,192 KiB (101.75 MiB)
peak RSS for the entire isolated benchmark process, including preparation,
proving, and verification. Allocation-tracked timings are not used above.

Logs: [release tests](results/ng-relations-release-tests.log),
[v8 timing](results/ng-relations-v8-timing.log),
[MLDSA-44](results/ng-relations-mldsa44-timing.log),
[MLDSA-65](results/ng-relations-mldsa65-timing.log),
[v8 tracked heap](results/ng-relations-v8-memory.log), and
[v8 process RSS](results/ng-relations-v8-rss.log).

## Previous pure constraint construction checkpoint

The numerical prover now runs directly on the main transcript. Its auxiliary
result contains each round's `L1(r)`, `L0(r)-L1(r)`, and `L2(r)`, each layer's
`alpha`, and the final dense input weights. Round interpolation coefficients are
computed once and shared with symbolic constraint construction. Final weights
are moved into the result; no intermediate dense vectors are cached.

The ZK constraint builder has no transcript or circuit argument. It performs no
assertion discovery or sampling, equality expansion, or contraction. Verification
independently derives equivalent data in sumcheck-ng and passes it to the same
builder. Auxiliary data remains local and is never serialized. A regression test
compares every auxiliary field and constraint coefficient, complete proof bytes,
and final transcript state against the pre-cleanup fingerprints and independent
derivation.

## Previous release validation and benchmarks

`cargo test --workspace --release` passed: 554 tests, zero failures, 23 ignored
by default (offline experiments and benchmarks). The NG crates also pass strict
Clippy with `-D warnings`; their release tests passed again after deleting the
unused polynomial reconstruction helper. The full suite includes stored legacy
proof compatibility and current mdoc integration tests. All 134 protected
legacy/shared files still match the pre-audit snapshot. The release-suite log is
[retained here](results/ng-aux-release-tests.log).

Fresh release/native binaries ran sequentially, pinned to CPU 2 with boost and
allocation tracking disabled. v8 uses the same two-attribute archive and circuit
IDs, one warmup and five measured runs; its figures are medians. MLDSA uses one
fresh-process run per variant with unchanged default circuit policies and IDs.
All benchmark proofs were serialized, parsed, and verified.

| Workload | Commit ms | Prove ms | Verify ms | Proof bytes |
|---|---:|---:|---:|---:|
| v8 full application flow | included | 280.251 | 139.096 | 308900 |
| MLDSA-44 | 289.405 | 803.708 | 635.687 | 200900 |
| MLDSA-65 | 329.851 | 940.427 | 741.812 | 211292 |

MLDSA prove excludes commitment, circuit compilation/loading, and serialization.
v8 full flow includes commitment, circuit loading, witness preparation, and
serialization. Proof sizes are unchanged from the previous auxiliary-replay
checkpoint. Compared with that checkpoint, measured prove time fell from
300.987 to 280.251 ms for v8, 844.485 to 803.708 ms for MLDSA-44, and 992.833 to
940.427 ms for MLDSA-65. These are separate timing batches.

The best recorded comparable v8 median remains 266.480 ms (fastest individual
run 266.119 ms), from the earlier observer implementation. Current hash-component
prove is 168.134 versus 160.237 ms in that run; signature prove is 33.219 versus
32.721 ms. Component timings and the full application flow are separate
measurements, so their medians do not form an additive phase breakdown.

A diagnostic isolated the safe indexed folding loop from the previous raw-pointer
loop. Six interleaved batches (safe/old/old/safe/safe/old), each with one warmup
and five measurements on CPU 2, gave these medians of batch medians:

| Folding implementation | Hash prove ms | Signature prove ms | Full flow ms |
|---|---:|---:|---:|
| Current safe indexed loop | 167.930 | 33.012 | 276.409 |
| Previous raw-pointer loop | 171.334 | 32.429 | 276.882 |

This does not support blaming the safe loop for the historical regression.
The current full-flow rerun also differs from the earlier 280.251 ms batch;
comparisons with the historical best include timing variation. The contraction
arithmetic is unchanged, and the current prover has no symbolic transcript
replay. The remaining hash-proving difference has not been attributed to a
specific code change. No speculative performance change was retained. Logs:
[safe 0](results/ng-bind-ab-0-safe.log), [old 1](results/ng-bind-ab-1-unsafe.log),
[old 2](results/ng-bind-ab-2-unsafe.log), [safe 3](results/ng-bind-ab-3-safe.log),
[safe 4](results/ng-bind-ab-4-safe.log), [old 5](results/ng-bind-ab-5-unsafe.log).

Current logs: [v8](results/ng-aux-v8-timing.log),
[MLDSA-44](results/ng-aux-mldsa44-timing.log), and
[MLDSA-65](results/ng-aux-mldsa65-timing.log).

## Historical auxiliary replay without an observer

This earlier checkpoint removed the observer. The numerical single-hand prover
returned
prover-local auxiliary data: one assertion count per layer and the final dense
input weights. A separate symbolic pass replayed transcript sampling and built
constraints using those weights. It did not repeat circuit scans, equality-table
expansions, or contractions. Auxiliary data was not serialized; production
verification independently derived all public weights.

At that checkpoint the regression test compared auxiliary replay against
independent symbolic verification, including every constraint coefficient, the final transcript, and
the complete proof bytes. All 39 runtime-proto/runtime-sumcheck/runtime-zk tests
and the workspace all-target compilation check passed.

The observer-based results below are historical. New no-observer baseline logs
are [v8](results/no-observer-v8-timing.log),
[MLDSA-44](results/no-observer-mldsa44-timing.log), and
[MLDSA-65](results/no-observer-mldsa65-timing.log). Those baseline runs replayed
the full symbolic weight calculation before the auxiliary shortcut was added.

Both batches used fresh release/native binaries, allocation tracking disabled,
boost disabled, and sequential processes pinned to CPU 2. v8 uses the same saved
two-attribute archive, one warmup, and five measured flows; its numbers are
medians. MLDSA uses one fresh-process run per variant, with the selected default
circuit policy. All proofs were serialized, parsed, and verified. These are
checkpoint measurements; no further tuning was performed.

| Workload and timed scope | Full symbolic replay ms | Auxiliary replay ms |
|---|---:|---:|
| v8 full prover flow, including commitment | 365.648 | 300.987 |
| MLDSA-44 prove, excluding commitment | 1154.794 | 844.485 |
| MLDSA-65 prove, excluding commitment | 1343.655 | 992.833 |

| Final auxiliary-replay workload | Commit ms | Prove ms | Verify ms | Proof bytes |
|---|---:|---:|---:|---:|
| v8 full application flow | included | 300.987 | 155.782 | 308900 |
| MLDSA-44 | 290.985 | 844.485 | 632.574 | 200900 |
| MLDSA-65 | 331.138 | 992.833 | 738.701 | 211292 |

Final logs: [v8](results/aux-replay-v8-timing.log),
[MLDSA-44](results/aux-replay-mldsa44-timing.log), and
[MLDSA-65](results/aux-replay-mldsa65-timing.log).

## Post-cleanup benchmark rerun

Fresh release builds of old hand-major (`66f1fee`) and the cleaned-up single-hand
implementation, both with `target-cpu=native`, timing instrumentation disabled,
and every process pinned to CPU 2 on the same Ryzen 9950X with boost disabled.
Compilation finished before timing began. Each MLDSA old/new pair uses identical
circuit IDs, stock LFC2 traversal and segmentation, period 4, a special round-0
slice, and no pluckers. Ligero block lengths are unchanged for MLDSA:
6,125 for MLDSA-44 and 6,143 for MLDSA-65.

| Workload and timed scope | Old hand-major ms | Current single-hand ms | Speedup |
|---|---:|---:|---:|
| v8, full prover flow | 330.692 | 266.480 | 1.24x |
| MLDSA-44, prove excluding commit | 993.239 | 795.112 | 1.25x |
| MLDSA-65, prove excluding commit | 1144.651 | 923.716 | 1.24x |

v8 figures are five-run medians after one warmup; full flow includes commitment,
decompression, witness preparation, and proof serialization. MLDSA figures are
one fresh-process measurement per version and variant, excluding commitment,
circuit compilation/loading, witness preparation, and serialization. All proofs
were serialized, parsed, and verified.

| MLDSA phase | 44 old ms | 44 current ms | 65 old ms | 65 current ms |
|---|---:|---:|---:|---:|
| commit | 287.688 | 286.485 | 328.208 | 326.847 |
| prove | 993.239 | 795.112 | 1144.651 | 923.716 |
| verify | 740.749 | 615.705 | 848.941 | 714.067 |
| commit + prove | 1280.926 | 1081.597 | 1472.859 | 1250.563 |

The earlier 1,222.517/1,438.836 ms measurements were the initial unoptimized
single-hand implementation, not old hand-major. The optimized pre-cleanup smoke
run measured 779.987/913.424 ms; the fresh post-cleanup run is within about 2%
of those single measurements. The old/new speedup remains about 1.24x, below 2x.

Raw rerun records: [v8 old](results/rerun-v8-old.log),
[v8 current](results/rerun-v8-new.log),
[MLDSA-44 old](results/rerun-mldsa44-old.log),
[MLDSA-44 current](results/rerun-mldsa44-new.log),
[MLDSA-65 old](results/rerun-mldsa65-old.log), and
[MLDSA-65 current](results/rerun-mldsa65-new.log).

## Prover duplication audit and v8 comparison

The initial implementation ran the numerical sumcheck prover and then replayed
the symbolic verifier. Both passes expanded chi, contracted the circuit to form
mu, and constructed the next dense weights. The prover now builds symbolic
constraints from the messages and challenges produced by its numerical pass.
The independent verifier still derives its own public weights.

The final audit also merged assertion discovery into witness evaluation and
removed an intermediate public-input clone. Per layer, the production single-hand
prover now has one witness-evaluation traversal, one contraction for `H = M w`,
and one for `mu = M^T chi`. It expands `chi` once and carries the fully expanded
`chi + alpha mu` to the next layer. There is no `eq2`, transcript replay, or
all-layer cache of dense field coefficients in this path. The two contractions
have different operands and both are required by the transition. Folded work
buffers are released before constructing the next weights.

A new regression compares the complete serialized proof and final transcript
with an independent numerical-plus-symbolic replay. The optimized prover produces
identical proof bytes. Legacy round-major retains its original transcript and
scalar-auxiliary path.

### Controlled v8 measurements

Two-attribute mdoc v8, identical saved LFA2 archive and circuit IDs, deterministic
seed 42, AMD Ryzen 9 9950X, boost disabled, pinned to logical CPU 2, Rust 1.99.1,
release with `target-cpu=native`. Each timing is the median of five measured runs
after one warmup. Allocation tracking is disabled for timing and enabled in
separate single-run binaries. Every stored proof is parsed and verified.

The old control is the hand-major implementation from commit `66f1fee`; the
identical benchmark source is copied into that tree. This comparison does not
substitute the retained round-major compatibility protocol for old hand-major.


| Implementation | Full prover ms | Full verifier ms | Proof bytes |
|---|---:|---:|---:|
| Old hand-major | 330.261 | 176.841 | 344,236 |
| Optimized single-hand | 267.515 | 136.215 | 308,900 |
| Single-hand, old block lengths | 268.433 | 137.514 | 310,988 |

The full prover takes 19.0% less time (1.23x speedup), below the requested 2x.
The initial single-hand implementation measured 362.892 ms before removing the
duplicate work; that earlier run is retained separately and is not interleaved
with the final old/new measurements. Full prover timing includes commitment,
circuit decompression, witness preparation, and serialization. Circuit compilation
and archive preparation are excluded. Component timings below exclude witness
preparation and circuit loading; prove excludes commitment.

| Implementation | Circuit | Commit ms | Prove ms | Verify ms | Sumcheck bytes |
|---|---|---:|---:|---:|---:|
| Old hand-major | hash | 25.776 | 208.803 | 115.054 | 19,840 |
| Old hand-major | sig | 40.426 | 45.223 | 55.368 | 34,624 |
| Single-hand | hash | 25.537 | 160.479 | 83.251 | 10,240 |
| Single-hand | sig | 38.212 | 32.768 | 46.471 | 17,984 |

Native block lengths change from hash/signature 5,246/4,445 to 5,264/4,310.
The old-block-length control isolates that choice, but its row counts still
change with the smaller pad layout; it is not identical Ligero geometry.
Hash/signature rows are 179/18 for old hand-major, 177/17 for native single-hand,
and 178/17 for single-hand using old block lengths.

| Implementation | Full prover peak extra heap | Full verifier peak extra heap |
|---|---:|---:|
| Old hand-major | 96,768,982 bytes | 39,350,856 bytes |
| Single-hand | 92,291,362 bytes | 50,309,248 bytes |

Each memory figure is peak additional tracked heap relative to that operation's
baseline, excluding preexisting archive storage. The single-hand verifier uses
more heap than old hand-major because the propagated functional is dense.
Assertion metadata collected during evaluation also consumes additional prover
heap; it avoids a separate term scan and is released layer by layer.

The [comparison harness](../../circuits/experimental/tests/v8_comparison.rs)
accepts `V8_PREPARE`, `V8_ARCHIVE`, `V8_LABEL`, `V8_GEOMETRY`, `V8_COMPONENTS`,
`V8_REPEATS`, and `V8_WARMUPS`. From `rust/`, prepare and benchmark with:

```sh
V8_PREPARE=/tmp/v8-two-attribute.archive cargo test --release -p circuits-experimental --test v8_comparison -- --ignored --nocapture --test-threads=1
cargo test --release -p circuits-experimental --test v8_comparison --no-run
V8_ARCHIVE=/tmp/v8-two-attribute.archive V8_LABEL=new V8_GEOMETRY=native taskset -c 2 cargo test --release -p circuits-experimental --test v8_comparison -- --ignored --nocapture --test-threads=1
```

For old hand-major, extract commit `66f1fee` into a separate tree, copy only this
harness there, and build from that tree's `rust/` directory using the same flags.
Use the same archive. Set `V8_GEOMETRY=old` for the block-length control.
For separate heap measurements, add `--features bench-memory` and set
`V8_REPEATS=1 V8_WARMUPS=0`. Build first, then run the printed test executable
directly to exclude Cargo overhead. Final raw records are
[old timing](results/v8-old-native-timing.log),
[new timing](results/v8-new-native-timing.log),
[block-length control](results/v8-new-old-timing.log),
[old memory](results/v8-old-native-memory.log),
[new memory](results/v8-new-native-memory.log), and
[control memory](results/v8-new-old-memory.log). The
[unoptimized timing](results/v8-unoptimized-native-timing.log) records the regression.

## Earlier MLDSA smoke measurements

One release timing run per circuit, x86-64, Rust 1.99.1, `target-cpu=native`,
deterministic RNG seed 42, 18-byte field and 3-byte subfield. Each proof is
serialized, parsed, and verified against its stored LFC2 circuit. Commit and
prove timings are separate; verification includes receiving the commitment.
Circuit compilation, compression, and proof serialization are outside these
cryptographic timings. These final runs are pinned to logical CPU 2 and are smoke
measurements, not repeated-run medians. Initial unoptimized single-hand prover
times were 1,222.517/1,438.836 ms. The final timing records are in
[the optimized log](results/single-hand-optimized-timing.log); these are not a
controlled comparison against historical hand-major MLDSA experiments.

Both circuits retain period 4, the special round-0 slice, no pluckers, and stock
compiler traversal and segmentation. Ligero uses `rateinv=4`, `nreq=128`, with
geometry optimized using the single-hand pad count.

| Circuit | Commit ms | Prove ms | Verify ms | Proof bytes | Block encoding |
|---|---:|---:|---:|---:|---:|
| MLDSA-44 | 286.606 | 779.987 | 615.041 | 200,900 | 6,125 |
| MLDSA-65 | 325.802 | 913.424 | 710.743 | 211,292 | 6,143 |

Both examples have 24 layers and 420 retained quadratic rounds. Their single-hand
sumcheck component is 888 field elements (15,984 bytes); the same layer widths
would require 1,728 field elements (31,104 bytes) in a two-hand protocol.
Single-hand commits 912 pad coordinates instead of 1,752. Including private
circuit inputs, the committed witness counts are 162,463 and 186,358.

These measurements use the stock LFC2 segmenter, whereas some historical grids
use offline reordered/template circuits. Their full-proof sizes and timings are
not a controlled before/after comparison. Halving the sumcheck rounds does not
imply halving complete proof size or runtime.

The initial implementation's separate allocation-tracking runs measured these
peak additional heap bytes. These precede the final prover fusion and assertion
metadata cleanup; current controlled v8 memory measurements are above:

| Circuit | Commit | Prove | Prover total | Verify |
|---|---:|---:|---:|---:|
| MLDSA-44 | 36,109,644 | 91,531,348 | 119,599,348 | 37,684,336 |
| MLDSA-65 | 41,171,700 | 95,901,172 | 127,884,772 | 42,009,664 |

Each operation excludes allocations already live at its start. Prover total
uses the pre-commit baseline and the maximum over commitment and proving; it is
not the sum of the first two columns. Circuit compilation and preexisting circuit
storage are excluded. Folded prover buffers are released before constructing the
next public coefficient vectors. All vectors are local to the current transition.

The initial [timing records](results/single-hand-timing.log) and
[allocation records](results/single-hand-memory.log) retain the circuit IDs,
geometry, proof sizes, and test outcomes.

## Circuit identity and mdoc

The protocol does not change circuit terms, numbering, segmentation, or IDs.
The checked MLDSA circuit IDs are:

- MLDSA-44: `e6f2d6e8e472f0fdb1abcf777045fdad87c7eee2e8b625d2e0889cdf0983393b`.
- MLDSA-65: `ecc1ac16609c00c674fe243ea2633d58c1b88af209193dc893a708d6156de9d1`.

Experimental mdoc v8 uses single-hand with unchanged circuit/archive IDs.
Regenerated Ligero block sizes are 4,310 for signature circuits and 5,264 for
hash circuits with one through four attributes. Historical registry entries and
their round-major parameters are unchanged. Experimental hand-major v8 proofs
are replaced, rather than retained as a third protocol.

## Validation and reproduction

- Core protocol, codec, and ZK suites: 39 tests passed, including the exact
  C++/RFC proof vector, transcript agreement, malformed/truncated proofs,
  wrong-protocol commitments, endpoint tampering, and endpoint-pad products.
- Prime- and binary-field tests check the propagated functional and independent
  assertion weights. A forged zero-round proof of a false assertion is rejected.
- Experimental regression suite: 61 passed, 8 ignored; the two ignored MLDSA
  proof benchmarks were run explicitly and passed.
- Current mdoc positive/negative/corruption tests and all three historical
  integration tests passed, including 141 historical prover/verifier cases.
- Workspace all-target checking passed. Strict Clippy passed for the changed
  runtime packages with `--no-deps` and the pre-existing
  `chunks_exact_to_as_chunks` lint disabled for this Rust toolchain.

Run from `rust/`:

```sh
cargo test -p runtime-proto -p runtime-sumcheck -p runtime-zk
cargo test -p mdoc-zk-runtime --release --test runtime_tests
cargo check --workspace --all-targets
cargo clippy --no-deps -p runtime-proto -p runtime-sumcheck -p runtime-zk --all-targets -- -D warnings -A clippy::chunks_exact_to_as_chunks
MLDSA_SUMCHECK_ORDER=single-hand cargo test -p circuits-experimental --release --test experimental_tests proof_benchmark -- --ignored --nocapture --test-threads=1
MLDSA_SUMCHECK_ORDER=single-hand cargo test -p circuits-experimental --release --features bench-memory --test experimental_tests proof_benchmark -- --ignored --nocapture --test-threads=1
```

The memory run uses a separate binary with allocation tracking enabled. Its
timings should not be substituted for the timing-only measurements above.
