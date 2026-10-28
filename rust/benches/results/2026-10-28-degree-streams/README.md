# Degree-separated LFC2 / sumcheck-v2 experiment

Upstream `v2` was fast-forwarded to `f9cb430` (2026-10-28). The experiment is
opt-in with `degree-separated`; the ordinary compiler and archived circuits
retain their existing format. The experimental compiler emits separate quadratic,
linear and constant streams with no reserved One input and no One layer copies.

## Circuit bytes

All sizes are exact bytes. Compression uses streaming `zstd::encode_all` at level
16 for both versions. V9 rows include the hash circuit, signature circuit and
input manifest in their LFA2 bundle; the 169-byte development-cache wrapper is
excluded. ML-DSA rows cover the complete verifier circuit.

| Circuit | LFC2 zstd | LFD2 zstd | Change | LFC2 uncompressed | LFD2 uncompressed | Change |
|---|---:|---:|---:|---:|---:|---:|
| v9-2 | 176134 | 177355 | +0.69% | 675774 | 650271 | -3.77% |
| v9-4 | 176756 | 177705 | +0.54% | 695394 | 675481 | -2.86% |
| mldsa-44 | 508205 | 504616 | -0.71% | 1732146 | 1675158 | -3.29% |
| mldsa-65 | 542487 | 520872 | -3.98% | 1972268 | 1860330 | -5.68% |

## Online timing

AMD Ryzen 9 9950X, boost disabled, release optimization 3, native CPU, LTO,
one codegen unit, rustc 1.99.1. Each process is pinned to logical CPU 2.
One discarded process warmup per version/circuit precedes seven paired samples.
The before/after order alternates between pairs. Our builds and validation jobs
finish before these samples. Allocation tracking is disabled.

Medians below include circuit/proof decoding, witness/public-input preparation,
commitment, proving/verifying, serialization and cleanup. Circuit compilation and
parameter selection are outside the timers. V9 starts with a zstd-compressed
bundle; ML-DSA starts with the uncompressed serialized circuit (its zstd size is
a storage measurement). V9 uses compact variant 0 and the
reference kernel. ML-DSA uses the ordinary sextic field with the same selected
Polygero configuration in both versions: `k=1024, s=25, n=4096, t=128`.

| Circuit | LFC2 prove ms | LFD2 prove ms | Change | LFC2 verify ms | LFD2 verify ms | Change | Proof bytes LFC2 → LFD2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| v9-2 | 186.148 | 174.861 | -6.06% | 93.950 | 92.789 | -1.24% | 184232 → 185000 |
| v9-4 | 203.234 | 187.771 | -7.61% | 100.665 | 98.383 | -2.27% | 186824 → 186472 |
| mldsa-44 | 847.191 | 761.104 | -10.16% | 401.295 | 364.966 | -9.05% | 178324 → 178932 |
| mldsa-65 | 971.463 | 883.780 | -9.03% | 454.331 | 426.767 | -6.07% | 187668 → 188148 |

All timed proofs verified. Each ML-DSA invocation also rejected a changed public
key outside the timers. Circuit identities and Fiat–Shamir challenges change,
so proof sizes can change through the queried Merkle paths as well as geometry.

## Memory

Uncompressed serialized bytes are not the full prover memory footprint. The
decoder retains delta dictionaries, macro segments and token vectors, and the
prover separately allocates witnesses, weights, pads and commitment state.

Decoded heap below is the circuit's owned vector/box allocation capacity, excluding
allocator metadata and stack values. Peak heap is the additional live allocation
peak of the complete online operation, measured separately with `bench-memory`.
The timing numbers from those allocation-instrumented runs are not used above.

| Circuit | Decoded circuit bytes LFC2 → LFD2 | Prover peak MiB LFC2 → LFD2 | Verifier peak MiB LFC2 → LFD2 |
|---|---:|---:|---:|
| v9-2 | 2306024 → 2306040 | 42.701 → 42.701 | 34.334 → 34.335 |
| v9-4 | 2377572 → 2395868 | 47.539 → 47.557 | 37.396 → 37.414 |
| mldsa-44 | 5151932 → 5216516 | 101.333 → 101.372 | 38.805 → 38.866 |
| mldsa-65 | 5753148 → 5709528 | 106.504 → 106.440 | 42.581 → 42.539 |

Removing One saves exactly one input slot per layer: 20 hash plus 21 signature
slots for v9, and 24 slots for either ML-DSA circuit. The new compiler also
removes 19 hash plus 20 signature unit-copy terms for v9, and 23 terms for ML-DSA.
These are small relative to the millions of remaining witness slots. The initial
in-memory prototype still uses four-u32 delta dictionary entries for every degree;
the unused input coordinates of linear/constant entries are zero.

All four uncompressed archives shrink. ML-DSA zstd sizes also shrink, while v9's
zstd sizes grow by less than one percent. Peak prover heap barely changes: removing
one slot per layer changes only a tiny fraction of the witness. The experiment
remains opt-in; timing, serialized size and live memory are assessed separately.

## Implementation and validation

[Format and reduction design](../../../core/proto/LFD2.md). Each layer has three
independent LFC2 delta/segment streams with two, one and zero input coordinates.
The compiler lowers missing factors without creating One nodes, renumbers the
user inputs, and preserves a separate square/product ordering within the quadratic
stream. Segmentation applies independently to each stream.

Sumcheck subtracts the public constant contribution before the dot-product rounds,
adds linear coefficients directly to the prover's bound tensor, and subtracts
`alpha * L(u)` from the claim passed to the next layer. Both parties apply the
same offsets in the symbolic constraints. No extra messages or pads are added.
The linear paths specialize coefficients +1/-1 to additions/subtractions.

The first experiment mixed squares and products in output order and enlarged
the two-attribute v9 bundle to 707,955 uncompressed / 198,302 zstd bytes. Retaining
the existing square/product grouping reduced this to 662,854 / 179,351 bytes.
A further correction preserves the old gate-order comparison key for missing
factors: they sort before real operands without allocating a One wire. This
gives the final sizes above and also recovers ML-DSA compression. Gate ordering
and macro alignment matter more than merely omitting affine input coordinates.

All 637 feature-enabled test cases are covered across partitioned passing runs;
[test-coverage.csv](test-coverage.csv) maps every case to its passing log. The
earlier parallel attempt was killed for memory pressure. Circuit tests were then
run serially and the remaining runtime/compiler tests with two threads. The
all-variant v9 integration and focused degree tests were rerun after the final
gate-order change. Verifier-only, prover-only, compiler-only and all-target builds
pass.

The upstream NEXT parameter test incorrectly forced packing degree one; its
expectation now uses the field's actual packing layout and the integration test
passes. The source-inventory check was run in a clean checkout containing these
changes, excluding the user's pre-existing untracked `streaming.rs` without
modifying it. The adjacent logs retain the original failures and their passing
reruns for review.
Focused tests cover prime and binary fields, multiple layers, a scalar linear layer
with zero rounds, serialization/ID preservation, truncation, expanded-term budgets,
invalid indices/affine assertion markers, and altered witnesses.

Raw data: [samples](samples.csv), [medians](medians.csv),
[sizes and memory](sizes-memory.csv), [geometry](geometry.csv).
The `before-*.log` / `after-*.log` files hold each complete online run;
`*-memory-*.log` are the separate allocation measurements.

## Reproduction

Use separate checkouts at upstream `f9cb430` and this experimental tree. Build
from each `rust` directory with identical `.cargo/config.toml` and release settings:

Apply [the baseline reporting patch](baseline-reporting.patch) to the upstream
checkout first. It only adds the same archive-saving, size and heap reporting
hooks used by the experiment. Use [the recorded dependency lock](Cargo.lock.txt)
as `rust/Cargo.lock` in both checkouts.

```sh
# Upstream baseline
cargo bench --no-run --bench mdoc_zk_bench_v9 --bench mldsa_bench_v2 --features testonly,experimental
# Experiment
cargo bench --no-run --bench mdoc_zk_bench_v9 --bench mldsa_bench_v2 --features testonly,degree-separated
```

Copy the emitted binaries to separate directories as `v9` and `mldsa`. Prepare
separate v9 cache directories by invoking each `v9` executable once with
`MDOC_V9_QUICK=1 MDOC_V9_SAMPLES=1 MDOC_V9_ATTRIBUTES=2` and then `=4`, setting
`MDOC_V9_CACHE` to the appropriate directory. Prepare the ML-DSA archives with
`MLDSA_BENCH_REPEATS=1 MLDSA_BENCH_SAVE_DIR=... ./mldsa all`. The save/report
hooks added to the baseline benchmark do not change the circuit or timed code.
Keep baseline and experimental caches separate.

Compile [the standalone paired driver](compare.rs) with Rust and pass those
directories in the following order (CPU affinity is fixed to logical CPU 2):

```sh
rustc --edition=2021 compare.rs -o compare
./compare BEFORE_BIN AFTER_BIN BEFORE_V9_CACHE AFTER_V9_CACHE BEFORE_MLDSA_ARCHIVES AFTER_MLDSA_ARCHIVES OUTPUT_DIR
```

For the independent heap runs, rebuild each version with `bench-memory` added
and run one sample per circuit using the same caches. Run the regression suite:

```sh
cargo test --lib --features testonly,degree-separated -- --test-threads=1
cargo check --all-targets --features testonly,degree-separated
```
