# Separate coefficient streams: degree-only experiment → unit-stream experiment

This follows the [v2 experiment](../2026-10-28-degree-streams/README.md)
on upstream `v2` at `f9cb430`. Feature `coefficient-separated` includes
`v2`: neither compiler nor circuits introduce a One input or its
layer copies. The ordinary compiler remains unchanged. The subsequent
[assertion experiment](../2026-10-28-assertion-streams/README.md) adds linear assertions.

## Representation

[unit-stream experiment](../../../core/proto/LFC3.md) has seven independently compressed arrays:
quadratic general/unit/assertion, linear general/unit, constant general/unit.
General means a coefficient other than zero or one. Fixed arrays omit coefficient
indices: quadratic entries have three coordinates, linear two, constant one.
Zero coefficients are assertion markers, not ordinary arithmetic zero terms.
Sumcheck traverses the arrays separately, avoiding coefficient lookup and
multiplication for unit terms. Quadratic assertions use their sampled challenge.

## Serialized sizes

Exact bytes; streaming zstd level 16. V9 includes the hash circuit, signature
circuit and manifest, excluding its 169-byte development-cache wrapper. ML-DSA
includes the complete verifier circuit. Splitting coefficients helps v9 storage,
but hurts ML-DSA storage with the present independent macro dictionaries.

| Circuit | degree-only experiment zstd | unit-stream experiment zstd | degree-only experiment uncompressed | unit-stream experiment uncompressed |
|---|---:|---:|---:|---:|
| v9-2 | 177355 | 157598 | 650271 | 575318 |
| v9-4 | 177705 | 158593 | 675481 | 593471 |
| ML-DSA-44 | 504616 | 542023 | 1675158 | 1730493 |
| ML-DSA-65 | 520872 | 563657 | 1860330 | 1925294 |

## Online timing

AMD Ryzen 9 9950X, boost disabled; rustc 1.99.1, native CPU, release opt-level 3,
LTO, one codegen unit. Processes are pinned to logical CPU 2. One discarded warmup
per version/circuit, then seven paired samples alternating before/after order.
Allocation tracking is disabled. Our builds and validation finish before timing.
This is a local experiment, without a statistical confidence interval or machine
isolation from unrelated processes. Compare versions within each paired run;
absolute medians from different experiment stages vary.

End-to-end timers include decoding, input/witness preparation, commitment,
proving/verification, serialization and cleanup. Compilation and parameter
selection are excluded. V9 starts from zstd; ML-DSA starts from raw circuit bytes.
V9 uses compact variant 0 and the reference kernel. ML-DSA uses the sextic field,
with the same parameters in both versions: `k=1024, s=25, n=4096, t=128`.

| Circuit | degree-only experiment prover ms | unit-stream experiment prover ms | degree-only experiment verifier ms | unit-stream experiment verifier ms | Proof bytes before → after |
|---|---:|---:|---:|---:|---:|
| v9-2 | 183.501 | 169.940 | 97.417 | 91.491 | 185000 → 184680 |
| v9-4 | 198.529 | 185.126 | 103.556 | 99.155 | 186472 → 187656 |
| ML-DSA-44 | 773.477 | 620.691 | 372.832 | 304.054 | 178932 → 178836 |
| ML-DSA-65 | 901.283 | 724.954 | 438.190 | 350.887 | 188148 → 187892 |

Proving improves by 6.8–7.4% for v9 and 19.6–19.8% for ML-DSA. Verification
improves by 4.2–6.1% and 18.4–19.9%, respectively. All timed proofs verify;
each ML-DSA invocation also rejects a changed public key outside its timers.
Circuit identities and challenges change, so queried Merkle paths can change proof size.

## Memory

All entries below are bytes. Serialized size is only one part of prover memory:
decoded dictionaries and token vectors, witnesses, weights, pads and commitment
state have separate allocations. Decoded heap counts owned vector/box capacities;
peak is additional live heap during the online operation, measured separately
with allocation tracking enabled. These are allocation measurements, not RSS.

| Circuit | Decoded heap degree-only experiment → unit-stream experiment | Prover peak degree-only experiment → unit-stream experiment | Verifier peak degree-only experiment → unit-stream experiment |
|---|---:|---:|---:|
| v9-2 | 2306040 → 2059344 | 44775304 → 44528608 | 36002722 → 35756026 |
| v9-4 | 2395868 → 2133136 | 49866900 → 49604168 | 39231382 → 38968650 |
| ML-DSA-44 | 5216516 → 5325408 | 106296220 → 106405112 | 40754456 → 38487708 |
| ML-DSA-65 | 5709528 → 5851028 | 111610019 → 111751519 | 44605836 → 42958088 |

The prover peak barely changes. ML-DSA verifier memory falls because assertion
challenge storage is sized directly to the assertion arrays rather than growing
while scanning terms.

## Expanded terms

Counts are unchanged by the coefficient split. Columns classify coefficients;
zero denotes serialized assertions. Constant zero entries are absent.

| Circuit | Degree | Zero/assertion | One | Other |
|---|---|---:|---:|---:|
| v9 hash-2 | quadratic | 18698 | 1339191 | 482479 |
| v9 hash-2 | linear | 0 | 223218 | 1330608 |
| v9 hash-2 | constant | 0 | 790911 | 203 |
| v9 signature | quadratic | 3958 | 66770 | 75068 |
| v9 signature | linear | 0 | 83725 | 12742 |
| v9 signature | constant | 0 | 33080 | 1118 |
| v9 hash-4 | quadratic | 22214 | 1585715 | 526147 |
| v9 hash-4 | linear | 0 | 255420 | 1451668 |
| v9 hash-4 | constant | 0 | 862291 | 307 |
| ML-DSA-44 | quadratic | 182193 | 1514287 | 2141814 |
| ML-DSA-44 | linear | 0 | 1947053 | 778765 |
| ML-DSA-44 | constant | 0 | 31595 | 95850 |
| ML-DSA-65 | quadratic | 209555 | 1566734 | 3226336 |
| ML-DSA-65 | linear | 0 | 2040319 | 884797 |
| ML-DSA-65 | constant | 0 | 38653 | 98166 |

## Reproduction and validation

Build the v9 and ML-DSA benches with `--features coefficient-separated`; add
`bench-memory` for the separate allocation measurements. Use fresh archives and
caches. The [paired driver](../2026-10-28-degree-streams/compare.rs) takes
`BEFORE_BIN AFTER_BIN BEFORE_V9_CACHE AFTER_V9_CACHE BEFORE_MLDSA AFTER_MLDSA OUTPUT`;
binary directories contain `v9` and `mldsa`. The
[inspection tool](inspect.rs) takes a v9 cache directory and ML-DSA archive
directory, validates circuit identities, and checks typed counts against a full
term expansion. It reads degree-only experiment, unit-stream experiment and assertion-stream experiment.

[Samples](samples.csv), [medians](medians.csv), before/after application logs,
and separate `*-memory-*.log` files accompany this report. The term CSV heap
column uses the current decoder layout; historical decoded allocation figures
in the table above come from each version's memory logs.

354 compiler/core/runtime regression tests passed at this stage, including codec
round trips, truncation/budgets, circuit identities, and true/false proofs over
GF128, P256 and FP24. Compiler-only, prover-only, verifier-only and all-target
build checks passed. The subsequent assertion stage reruns 356 relevant tests,
including Boolean-window equivalence and direct assertion lowering. The source
inventory test is excluded because the workspace contains the user's pre-existing
untracked `streaming.rs`; that file is untouched. Application and mdoc unit suites
are outside this focused run; all four benchmark application proofs are exercised.
