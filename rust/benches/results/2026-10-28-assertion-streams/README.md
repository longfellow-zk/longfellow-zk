# Linear and quadratic assertions: unit-stream experiment → assertion-stream experiment

Feature `assertion-separated` includes `coefficient-separated` and
`v2`. It uses the eight-array [assertion-stream experiment format](../../../core/proto/LFC3.md).
There is no reserved One input or copied One wire. This follows the
[coefficient split](../2026-10-28-coefficient-streams/README.md), on upstream
`v2` at `f9cb430`.

`assert0(a*b)` lowers directly to a quadratic assertion over the factors, avoiding
the product value wire when it is otherwise unused. An assertion on an already
computed value becomes linear, instead of a quadratic square-zero marker.
Nonzero scalar factors can be discarded for assertions. Ordinary products needed
elsewhere remain computed. Final output zero checks remain implicit.

Linear assertions contribute their sampled `rho` directly to sumcheck's affine
left coefficient and its public linear correction. Quadratic assertions retain
the product binding. Neither adds a sumcheck round or masked message.

## Serialized sizes

Exact bytes, zstd level 16. V9 sizes include hash, signature and manifest in the
bundle, excluding its 169-byte cache wrapper. ML-DSA covers its verifier circuit.

| Circuit | unit-stream experiment zstd | assertion-stream experiment zstd | unit-stream experiment uncompressed | assertion-stream experiment uncompressed |
|---|---:|---:|---:|---:|
| v9-2 | 157598 | 157611 | 575318 | 574590 |
| v9-4 | 158593 | 158615 | 593471 | 593582 |
| ML-DSA-44 | 542023 | 541420 | 1730493 | 1731719 |
| ML-DSA-65 | 563657 | 563659 | 1925294 | 1927696 |

For comparison with the original upstream format, before any of these three
experiments:

| Circuit | Original LFC2 zstd | Final assertion-stream experiment zstd | Original LFC2 raw | Final assertion-stream experiment raw |
|---|---:|---:|---:|---:|
| v9-2 | 176134 | 157611 | 675774 | 574590 |
| v9-4 | 176756 | 158615 | 695394 | 593582 |
| ML-DSA-44 | 508205 | 541420 | 1732146 | 1731719 |
| ML-DSA-65 | 542487 | 563659 | 1972268 | 1927696 |

## Paired online timing

The same method and machine as the coefficient report: Ryzen 9 9950X, boost off,
native release build, one warmup then seven alternating paired samples, CPU 2,
allocation tracking off. Timers include decoding, input/witness preparation,
commitment, proving/verification, serialization and cleanup; compilation and
parameter selection are excluded. V9 decodes zstd; ML-DSA decodes raw circuits.
All four proofs verify, and both ML-DSA cases reject changed public keys.

| Circuit | unit-stream experiment prover ms | assertion-stream experiment prover ms | unit-stream experiment verifier ms | assertion-stream experiment verifier ms | Proof bytes before → after |
|---|---:|---:|---:|---:|---:|
| v9-2 | 166.058 | 165.383 | 90.199 | 89.265 | 184680 → 185352 |
| v9-4 | 177.520 | 179.103 | 94.740 | 93.862 | 187656 → 187144 |
| ML-DSA-44 | 624.350 | 626.135 | 307.952 | 305.630 | 178836 → 178868 |
| ML-DSA-65 | 718.927 | 722.571 | 349.299 | 349.200 | 187892 → 187956 |

The assertion split removes wires but does not show a consistent additional
prover speedup: changes range from −0.4% to +0.9%. Verifier changes are also small.
The earlier coefficient split supplies the substantial timing improvement.
These local medians have no statistical confidence interval; compare each
stage's paired runs rather than combining absolute timings across stages.

## Memory

Bytes below are owned decoded circuit allocations and additional live online
peak heap, measured with allocation tracking separately from timing. They are
not RSS. Serialized bytes do not include witness/commitment working memory.

| Circuit | Decoded heap unit-stream experiment → assertion-stream experiment | Prover peak unit-stream experiment → assertion-stream experiment | Verifier peak unit-stream experiment → assertion-stream experiment |
|---|---:|---:|---:|
| v9-2 | 2059344 → 2057220 | 44528608 → 44526228 | 35756026 → 35753710 |
| v9-4 | 2133136 → 2133980 | 49604168 → 49604852 | 38968650 → 38969302 |
| ML-DSA-44 | 5325408 → 5328968 | 106405112 → 106383664 | 38487708 → 38491316 |
| ML-DSA-65 | 5851028 → 5859152 | 111751519 → 111654715 | 42958088 → 42966308 |

## Assertion counts and removed wires

These counts cover serialized assertions. Final zero-output checks are implicit
and excluded. The direct-product count is also the number of removed product
wires for these circuits.

| Circuit | Quadratic assertions | Linear assertions | Product wires removed |
|---|---:|---:|---:|
| v9 hash-2 | 9921 | 8777 | 9921 |
| v9 signature | 0 | 3958 | 0 |
| v9 hash-4 | 12475 | 9739 | 12475 |
| ML-DSA-44 | 1042 | 181151 | 1042 |
| ML-DSA-65 | 4372 | 205183 | 4372 |

## Expanded terms by type

Zero entries are assertion markers; the other columns describe arithmetic terms.

| Circuit | Degree | Zero/assertion | One | Other |
|---|---|---:|---:|---:|
| v9 hash-2 | quadratic | 9921 | 1329270 | 482479 |
| v9 hash-2 | linear | 8777 | 223218 | 1330608 |
| v9 hash-2 | constant | 0 | 790911 | 203 |
| v9 signature | quadratic | 0 | 66770 | 75068 |
| v9 signature | linear | 3958 | 83725 | 12742 |
| v9 signature | constant | 0 | 33080 | 1118 |
| v9 hash-4 | quadratic | 12475 | 1573240 | 526147 |
| v9 hash-4 | linear | 9739 | 255420 | 1451668 |
| v9 hash-4 | constant | 0 | 862291 | 307 |
| ML-DSA-44 | quadratic | 1042 | 1513245 | 2141814 |
| ML-DSA-44 | linear | 181151 | 1947053 | 778765 |
| ML-DSA-44 | constant | 0 | 31595 | 95850 |
| ML-DSA-65 | quadratic | 4372 | 1562362 | 3226336 |
| ML-DSA-65 | linear | 205183 | 2040319 | 884797 |
| ML-DSA-65 | constant | 0 | 38653 | 98166 |

## Validation and artifacts

356 relevant compiler/core/runtime tests passed, covering both assertion kinds,
false linear inputs (including when input wire zero contains zero), direct
product lowering without product wires, GF128/P256/FP24 arithmetic and codec
round trips, malformed/truncated archives, expanded budgets, authenticated IDs,
and Boolean-window equivalence for windows 1–4. Compiler-only, prover-only,
verifier-only and all-target checks pass. Application and mdoc unit suites are
outside this focused run; all four application benchmark proofs verify.
The source inventory check is excluded due to the user's pre-existing untracked
`streaming.rs`, which is untouched.

Build the benches with `--features assertion-separated`, and add `bench-memory`
only for separate allocation measurements. Use fresh caches. Reproduction uses
the same [paired driver](../2026-10-28-degree-streams/compare.rs) and
[inspection tool](../2026-10-28-coefficient-streams/inspect.rs) as the coefficient
report. [Samples](samples.csv), [medians](medians.csv),
[before term counts](before-terms.csv), [after term counts](after-terms.csv),
application logs, memory logs and focused test/build logs accompany this report.
The term CSV heap column uses the current decoder layout; the historical
allocation table uses each binary's memory log.
