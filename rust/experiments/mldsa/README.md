# MLDSA analysis support

## Current integration

The experimental circuits are now integrated on the `mldsa` branch with its shared
type/output-major compiler ordering and the
[single-hand sumcheck protocol](../../runtime/sumcheck-ng/README.md).
The single-hand runtime lives in the separate `runtime-sumcheck-ng` and
`runtime-zk-ng` crates. The compiler is shared and produces NG circuits only.
The selected default for both MLDSA-44 and MLDSA-65 is period 4, a special
round-0 slice, and no bit pluckers (direct XOR-basis witnesses). Cuts follow
zero-based rounds [0,3,7,11,15,19,23]. Default builds ignore experiment environment
variables; compilation and native witness generation share this policy.
The earlier grid's whole / shape_classes / reuse ordering produced compressed
circuits of 367,947 / 377,432 bytes and hand-major proofs of 218,708 / 227,852
bytes. Current stock-segmentation single-hand measurements are in
[SINGLE_HAND_REPORT.md](SINGLE_HAND_REPORT.md). Protocol replacement preserves
the compiler and slicing policy; experimental mdoc v8 also uses single-hand.
Historical reports describe older worktrees, not the current runtime.
Some opt-in Morton/template analysis helpers assume a
Morton-ordered input circuit; they are not part of the default proof path.

Timing benchmarks use `--features testonly`, without `bench-memory`. Separate
`--all-features` benchmark runs enable a test-binary allocation tracker and print
commit/prove/verify peak additional heap. Run each benchmark alone with
`--test-threads=1`; concurrent tests would invalidate those heap measurements.
Whole-process RSS, measured separately with `/usr/bin/time -v`, also includes
compilation of the circuit and compression, so it is not per-operation memory.

## Historical analysis helpers

These offline helpers are retained for the experimental Rust MLDSA tests. They
were moved from `compile/compiler/experiments` when the production compiler,
mdoc code, and sumcheck runtime were restored to `HEAD`.

The legacy entry point is included by `tests/all/mldsa_verifier.rs`. The following
invocation is historical and requires an appropriate Morton-ordered control:

```sh
MLDSA_SLICE_PERIOD=6 MLDSA_FIRST_ROUND=0 MLDSA_PLUCKER_BITS=0 cargo test -p circuits-experimental --features mldsa-slicing-experiment analyze_mldsa44_morton -- --ignored --nocapture
```

The older reports and result files are historical comparison records, including mdoc
controls used during MLDSA research. Their measurements and original source paths
refer to the earlier experimental worktree, not the restored production scheduler.
They have not been regenerated. In particular, the experimental non-Morton
comparison-sort sumcheck adaptation and mdoc benchmark hooks are no longer in production code.

All C++ source is as committed. The two uncommitted C++ benchmark harnesses were
removed from this worktree and saved with the rollback recovery files in `/tmp`.

## Validation and benchmarks

[Relative segment references](RELATIVE_SEGMENTS_REPORT.md) prototypes ID-preserving
three-coordinate segment offsets, with 112 size controls on selected MLDSA,
mdoc, and historical whole-instance/boundary-aware circuits. It preserves exact
term streams and proof bytes. The small selected-MLDSA savings do not justify a
production format change and do not carry over to mdoc; LFR1 remains experimental.

[Balanced-plucker hand-major grid](PLUCKER_GRID_REPORT.md) sweeps periods 1–6,
maximum packed widths 0–6, and a special round-0 cut off/on for both MLDSA
circuits. Build with `mldsa-slicing-experiment` and use `MLDSA_SLICE_PERIOD`,
`MLDSA_PLUCKER_BITS` (0 = direct XOR witnesses), and `MLDSA_FIRST_ROUND` (0/1).
Widths within each 64-bit lane differ by at most one; circuit allocation and
native witness generation share the same partition. The runner measures saved
LFC2 circuits, so its fresh-process peak RSS excludes compilation/compression.
Its explicit `ORDER_TOTAL_TERM_LIMIT=40000000` permits the largest locally
generated cells; the production reader's default remains 20 million terms.
The current rerun sets `subfield_boundary = ninput` and uses 3-byte fp24 /
18-byte fp24_6 serialization, including those sizes in proof-geometry selection.
These new artifacts live in `target/plucker-grid-sf18`; old 24/4-byte artifacts
cannot be loaded by the new experimental field reader.

[First-round slicing and period sweep](FIRST_ROUND_SLICE_REPORT.md) records the
earlier period 1–6 sweep, vanilla Morton controls, and finer extraction.
`mldsa-first-round-slice` remains a legacy alias for `mldsa-slicing-experiment`.
With either feature, the environment can override the selected defaults
(`MLDSA_SLICE_PERIOD=4`, `MLDSA_FIRST_ROUND=1`, `MLDSA_PLUCKER_BITS=0`).
Use the same configuration to compile circuits and generate proof witnesses.
Default builds ignore these variables. Regenerate old circuits and witnesses
when switching slicing policies; their layouts and circuit IDs differ.

[Core byte audit](CORE_BYTE_AUDIT_REPORT.md) separates shared-core, residual and
mixed LFC2 storage, traces the expensive SHAKE boundary exceptions, and discusses
source-level options without changing the circuits.

LTP1 has been abandoned and its runtime support removed. Template discovery is
now an offline ordering experiment producing ordinary LFC2 files; the prover and
verifiers see no templates or maps. The historical LTP1 measurements remain in
[LAYER_TEMPLATE_REPORT.md](LAYER_TEMPLATE_REPORT.md), not as current benchmarks.
The replacement experiment and same-runtime performance comparisons are in
[TEMPLATE_ORDER_LFC2_REPORT.md](TEMPLATE_ORDER_LFC2_REPORT.md). Template-guided
traversals did not beat the existing shared LFC2 policy, which remains unchanged.
The follow-up [TEMPLATE_WIRE_LFC2_REPORT.md](TEMPLATE_WIRE_LFC2_REPORT.md) also
renumbers internal wires and reuses exact template interiors in ordinary LFC2.
That single experimental rule saves 2.1%/3.7% compressed on MLDSA-44/65 and 3.4%
on the two-attribute mdoc archive, with mixed raw-size trade-offs. It is opt-in;
original input/output positions and production defaults remain unchanged.
The next [TEMPLATE_CORE_LFC2_REPORT.md](TEMPLATE_CORE_LFC2_REPORT.md) removes
exceptional terms from shared templates and emits them as an ordinary residual
stream. With the same numbering/segmentation rule, MLDSA drops further to
889,499 / 901,065 bytes zstd-22; the combined mdoc archive is essentially flat
at 156,667 bytes. No patch format or runtime mapping support is added.

The offline LCT1 segmentation sweep is documented in
[LCT_SEGMENTATION_REPORT.md](LCT_SEGMENTATION_REPORT.md). It preserves exact LCT1
bytes and does not change production formats or proving.

Current results are in [DENSE_KIND_BENCHMARK_REPORT.md](DENSE_KIND_BENCHMARK_REPORT.md).
Historical restored-baseline results and cleanup checks are recorded in
[HEAD_VALIDATION_REPORT.md](HEAD_VALIDATION_REPORT.md).

Run these from the Rust workspace root:

```sh
cargo check -p circuits-experimental --no-default-features --lib
cargo check -p circuits-experimental --no-default-features --features mldsa-runtime --lib
cargo test -p circuits-experimental --all-features --all-targets
cargo test --release -p circuits-experimental --features testonly mldsa44_proof_benchmark -- --ignored --nocapture --test-threads=1
cargo test --release -p circuits-experimental --features testonly mldsa65_proof_benchmark -- --ignored --nocapture --test-threads=1
```

For default-policy measurements, unset `MLDSA_WIRE_POLICY`, `MLDSA_LANE_ORDER`, and
`MLDSA_TEMPLATE_ROUNDTRIP`. These opt-in hooks retain the earlier offline
experiments; they do not affect the default circuit. Run timing benchmarks
sequentially, without concurrent builds or tests.

Both proof benchmarks use the selected period-4/round-0/no-plucker default,
the current shared compiler and runtime, and the
first committed C++ vector for their parameter set. They decode the segmented
LFC2 circuit with circuit-ID checking, round-trip the serialized proof, and verify
the decoded proof. Reported `commit`, `prove`, and `verify` timings exclude
circuit compilation, encoding, compression, and proof serialization/deserialization.
Total prover time is `commit + prove`; the printed `total` is the entire test.

These circuits verify a signature on a supplied `mu` against an expanded public
key. Key expansion and message-to-`mu` hashing happen in native witness setup;
the test makes the expanded key public and supplies `mu` privately. They are not
a complete application circuit binding a public message to its digest.
