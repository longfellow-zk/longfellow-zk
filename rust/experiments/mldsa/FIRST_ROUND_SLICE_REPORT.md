# First-round SHAKE slicing, period sweep, and vanilla Morton controls

2026-09-12. Experimental Rust MLDSA-44/65, same field, XOR basis, CRT and signature
relations. No production scheduler, prover/verifier algorithm, C++ or mdoc source
was changed by this experiment. The worktree contains earlier unrelated changes.

## Outcome

An extra witnessed cut after Keccak round 0 isolates absorption-specific wiring.
With the existing whole-template wire numbering and shared-core LFC2 ordering,
period 6 produces **434,599 / 439,407 zstd-22 bytes**, versus **889,499 / 901,065**
without that cut. Both are below the strict 500,000-byte target, and are ordinary
LFC2 directly consumed by the existing hand-major prover.

The original finer-fragment ordering experiment was also completed. It did not
produce a broadly useful policy: gains in fragment coverage were offset by
boundary/dictionary/token overhead, and mdoc regressed. It remains opt-in.

## Precisely which schedules were tested?

The additional cut is after round 0, not before it. Regular cuts remain aligned
to the original round numbering: cut after completed rounds divisible by P,
and always after round 23. Thus P=6 is **0,5,11,17,23**, i.e. chunks **1,5,6,6,6**.
It is not the shifted schedule 0,6,12,18,23.

All P=1..6 runs retain the first-round cut. At P=1 it coincides with an existing
cut and is counted only once. The numbers of states per permutation are
24, 13, 9, 7, 6, 5. Both verifiers have eight SHAKE permutations; each added state
has 1,600 XOR-basis witnesses with range and packed transition checks.

The default build still uses period 6 without the extra cut. Enable the opt-in
Cargo feature `mldsa-first-round-slice`; only that build consults
`MLDSA_SLICE_PERIOD` (1..6, default 6). The value is cached once per process so
compilation and native witness generation cannot silently switch schedules
mid-run. Use separate processes for different periods. Circuit compilation and
proof witness generation must use matching configurations.

## Circuit sizes

Every entry below is bytes, raw LFC2 / whole-file zstd-22. No mapping, dictionary,
header or exception overhead is omitted.

| Period | Core ML44 raw / z22 | Core ML65 raw / z22 | Morton ML44 raw / z22 | Morton ML65 raw / z22 |
|---:|---:|---:|---:|---:|
| 1 | 1,325,592 / 215,327 | 1,491,568 / 222,306 | 4,360,579 / 1,321,898 | 4,672,467 / 1,338,423 |
| 2 | 1,520,334 / 277,585 | 1,683,536 / 285,461 | 5,462,364 / 1,960,841 | 5,583,483 / 1,980,563 |
| 3 | 1,594,336 / 330,412 | 1,757,847 / 338,087 | 5,785,604 / 2,236,200 | 5,706,741 / 2,216,246 |
| 4 | 1,649,067 / 368,227 | 1,812,271 / 374,245 | 5,919,673 / 2,489,200 | 5,947,419 / 2,509,271 |
| 5 | 1,700,712 / 400,626 | 1,864,519 / 409,355 | 6,105,886 / 2,830,912 | 6,253,654 / 2,852,062 |
| 6 | 1,752,554 / 434,599 | 1,913,185 / 439,407 | 6,433,548 / 3,065,476 | 6,532,233 / 3,081,648 |

The core policy is always `whole / shape_classes / reuse`; it does not select a
policy based on the measured size. The Morton control keeps original compiled
wire IDs, sorts all terms by absolute Morton input-pair order (then g and
coefficient), and uses ordinary compiler segmentation. It does not use component
ordering or template-driven renumbering. Both layouts pass exact term-multiset
checks and LFC2 roundtrips for every circuit; LFC1 serialization is also measured.

Without the extra first-round cut, period-6 controls are:

| Layout | MLDSA-44 raw / zstd-22 | MLDSA-65 raw / zstd-22 |
|---|---:|---:|
| Core | 2,628,172 / 889,499 | 2,761,654 / 901,065 |
| Vanilla Morton | 7,275,471 / 3,776,435 | 7,361,859 / 3,800,283 |

The first-round slice helps vanilla Morton at P=6 too, but only to 3.07 / 3.08 MB.
Even its smallest P=1 files are 1.32 / 1.34 MB. None meets 500 KB. For these tested
policies, reaching the target requires the core layout as well as the source cut.

At P=6, even before template reordering, the source's ordinary default-ordered
LFC2 files are 531,455 / 566,027 zstd-22 bytes. The same existing core policy then
takes them below the target; no fine-fragment policy is needed.

LFC1 and zstd-16 measurements for every variant are in
[the size CSV](results/slice-sweep-sizes.csv). For example P=6 core LFC1 is
79,418,589 / 95,894,817 raw bytes and 380,428 / 387,941 zstd-22 bytes. The recommended
LFC2 files remain compact in memory and do not require expanding LFC1.

## Geometry and proof implications

| Period | States/permutation | Layers | Inputs 44 / 65 | Wires 44 / 65 | Terms 44 / 65 |
|---:|---:|---:|---:|---:|---:|
| 1 | 24 | 11 | 384,272 / 412,263 | 3,838,977 / 4,015,597 | 7,342,255 / 8,713,898 |
| 2 | 13 | 12 | 243,472 / 271,463 | 3,690,362 / 3,868,342 | 6,918,464 / 8,291,467 |
| 3 | 9 | 18 | 192,272 / 220,263 | 3,639,168 / 3,817,148 | 6,767,206 / 8,140,209 |
| 4 | 7 | 24 | 166,672 / 194,663 | 3,613,574 / 3,791,554 | 6,691,580 / 8,064,583 |
| 5 | 6 | 30 | 153,872 / 181,863 | 3,601,364 / 3,779,344 | 6,654,354 / 8,027,357 |
| 6 | 5 | 36 | 141,072 / 169,063 | 3,587,986 / 3,765,966 | 6,615,960 / 7,988,963 |

These are total circuit wires including inputs, not just witness counts. Public
input counts remain 5,121 / 9,217. Layout changes within each period leave all
geometry fixed; source slicing changes witness allocation and circuit IDs.

Original P=6 without the first-round cut had 128,272 / 156,263 inputs,
3,577,829 / 3,756,007 wires, 6,580,787 / 7,953,988 terms, and 37 layers.
Adding the first cut at P=6 adds **12,800 input witnesses** to either circuit,
35,173 / 34,975 terms, and 10,157 / 9,959 total wires. Depth falls to 36: the
absorption-specific prefix is no longer part of a full six-round unsliced chunk.

The input numbering is fixed by the wire-ordering pass *within each compiled
circuit*. Adding source witnesses changes the witness ABI; old proofs/IDs are
not interchangeable with the new configuration.

## Runtime, proof size, and actual peak RSS

All cases use the same existing prover/verifier implementations and CRT geometry
optimizer. Core files select hand-major; Morton files select round-major on
**both** sides, including the symbolic verifier. Timing differences therefore
compare the complete requested layout/protocol configurations, not traversal
alone with the sumcheck schedule held fixed.

Times below are medians of five complete proof/verify flows per case, run
serially after all compilation and compression jobs finished, on the same Ryzen
9950X release/native build. Prover time includes commitment plus proving;
circuit loading/ID checks, witness construction and proof serialization/parsing
are outside the timed regions. CSVs also report load and commitment timings.

Peak RSS is the OS high-water mark from a **separate fresh process with one
proof/verify flow**, measured by `/usr/bin/time -v`. It includes loaded circuit,
witness construction, proving, verification and process overhead, but no circuit
compilation. It is not an estimated heap count or a sum of per-phase maxima.
Five-repetition high-water marks are also retained in the summary CSV; allocator
retention can make those considerably larger.

### MLDSA-44

| Period | Layout / protocol | Proof bytes | Prover ms | Verifier ms | Fresh peak RSS MiB |
|---|---|---:|---:|---:|---:|
| 6, no first cut | Core / hand | 665,544 | 1080.4 | 652.3 | 120.92 |
| 6, no first cut | Morton / round | 665,096 | 1357.3 | 661.5 | 136.00 |
| 1 | Core / hand | 1,140,136 | 1588.4 | 945.9 | 191.96 |
| 1 | Morton / round | 1,139,944 | 1793.1 | 966.2 | 224.36 |
| 2 | Core / hand | 845,976 | 1336.2 | 799.3 | 148.52 |
| 2 | Morton / round | 845,176 | 1578.3 | 807.5 | 162.11 |
| 3 | Core / hand | 820,632 | 1211.4 | 763.2 | 134.61 |
| 3 | Morton / round | 821,272 | 1484.6 | 777.9 | 148.45 |
| 4 | Core / hand | 745,048 | 1141.5 | 709.5 | 127.36 |
| 4 | Morton / round | 744,632 | 1421.1 | 724.5 | 141.13 |
| 5 | Core / hand | 710,328 | 1114.6 | 685.9 | 122.46 |
| 5 | Morton / round | 711,384 | 1389.1 | 696.1 | 136.67 |
| 6 | Core / hand | 694,424 | 1087.7 | 669.4 | 119.73 |
| 6 | Morton / round | 694,488 | 1381.6 | 677.6 | 134.38 |

### MLDSA-65

| Period | Layout / protocol | Proof bytes | Prover ms | Verifier ms | Fresh peak RSS MiB |
|---|---|---:|---:|---:|---:|
| 6, no first cut | Core / hand | 719,176 | 1204.6 | 731.4 | 129.75 |
| 6, no first cut | Morton / round | 718,920 | 1452.6 | 748.0 | 144.91 |
| 1 | Core / hand | 1,199,528 | 1738.7 | 1033.8 | 234.37 |
| 1 | Morton / round | 1,199,528 | 1919.1 | 1053.2 | 242.26 |
| 2 | Core / hand | 879,384 | 1448.6 | 852.2 | 157.70 |
| 2 | Morton / round | 879,256 | 1668.3 | 880.5 | 171.18 |
| 3 | Core / hand | 903,864 | 1366.7 | 858.2 | 145.04 |
| 3 | Morton / round | 904,056 | 1606.3 | 877.3 | 156.84 |
| 4 | Core / hand | 823,896 | 1298.1 | 803.8 | 136.49 |
| 4 | Morton / round | 824,024 | 1546.7 | 827.8 | 149.68 |
| 5 | Core / hand | 794,200 | 1271.6 | 778.9 | 131.90 |
| 5 | Morton / round | 794,200 | 1505.0 | 805.4 | 145.64 |
| 6 | Core / hand | 759,256 | 1239.0 | 756.1 | 129.13 |
| 6 | Morton / round | 759,128 | 1480.7 | 765.0 | 143.71 |

Small proof-size differences between core and Morton at fixed geometry come
from circuit IDs/transcript schedules and multiproof sharing; they are not
witness-count savings. Proof lengths use the benchmark's fixed input and seed,
not a claimed worst-case bound.

Proof size is not strictly monotonic in period. For example ML65 P=2 has fewer
protocol constraints but more witnesses than P=3; the automatically chosen
Ligero/CRT `block_enc` changes from 7,817 to 6,125. Both layer count and discrete
proof geometry matter, not just the input witness count.

### Recommendation

**Keep period 6 and add the first-round cut for the core-layout experiment.**
It meets 500,000 bytes on both circuits and has the smallest proofs and fastest
prover among the tested first-cut periods. It avoids changing the shared
scheduling policy or adding a new storage format.

Relative to the previous P=6 core candidate, proof size increases by
**28,880 / 40,080 bytes (4.34% / 5.57%)**. Prover time increases by
**0.67% / 2.85%**, verifier time by **2.62% / 3.37%**. Fresh peak RSS is essentially
unchanged (120.92 → 119.73 MiB, 129.75 → 129.13 MiB); these single-run RSS readings
should not be interpreted as a statistically established memory improvement.

For stricter circuit-storage targets, smaller periods give measured tradeoffs,
but they add witnesses/proof bytes and are slower. P=1 is the smallest circuit
in this sweep, not the best configuration under the stated 500 KB target.
Vanilla Morton does not meet that target at any tested period.

### Validation and result files

- All 24 sliced period/layout/circuit cases passed exact term-multiset and
  LFC2 roundtrip/ID checks; both unsliced Morton controls passed too.
- All **140 timed plus 28 fresh-process proof/verify flows passed**.
- **53 MLDSA tests passed at each period** (318 total), including SHAKE,
  arithmetic, sampling and invalid-witness tests. The SHAKE transition test flips
  a valid ±1 state bit, ensuring rejection is not merely a range-check failure.
- Both schedule tests passed with and without the feature; all 42 ordering-harness
  tests passed. Workspace/all-targets/all-features check passed without warnings.
- P=6 exports and saved core LFC2 files are byte-identical to the initially
  measured first-round-slice artifacts. Defaults remain unchanged.

[Summary including fresh RSS](results/slice-sweep-summary.csv),
[all timing samples](results/slice-sweep-timings.csv),
[circuit sizes including LFC1 and zstd-16](results/slice-sweep-sizes.csv),
[geometry](results/slice-sweep-geometry.csv).

## Causal audit at period 6

The audit was rerun on both first-round-sliced circuits, verifying the fresh source
against its exported circuit and the core traversal against its saved LFC2 ID
and exact term stream.

| Exact raw-byte ownership | MLDSA-44 before / after | MLDSA-65 before / after |
|---|---:|---:|
| Core-only, including boundaries | 1,712,493 / 1,545,125 | 1,808,385 / 1,667,548 |
| Exception-only | **811,644 / 173,174** | **820,132 / 210,872** |
| Shared between core and exception | 76,932 / 7,192 | 105,842 / 7,509 |
| Constants, headers, ID | 27,103 / 27,063 | 27,295 / 27,256 |

Unmatched SHAKE terms fall from 243,523 / 245,377 to 46,831 / 48,560. Their
assertion paths now end at **round 0**, rather than round 5. The following
five-round chunk starts from a uniform witnessed state and can share its core.
This is direct evidence for the boundary-specialization hypothesis.

Compressing exclusively SHAKE-owned bytes alone gives 276,122 / 281,757 bytes,
down from 738,805 / 743,329. As explained in
[the original byte audit](CORE_BYTE_AUDIT_REPORT.md), such isolated compression
figures are diagnostic, not additive contributions to the whole compressed file.

## Finer-grained extraction: attempted, not adopted

The prototype leaves existing whole-template cores untouched and searches the
unmatched-program residue for exact translated fragments. It tests complete
per-output shape groups, chunks of 8 or 2 terms within those groups, and windows
of 32 or 128 terms across outputs. Keys contain normalized g/h0/h1 coordinates
and every coefficient. Only repeated exact fragments are extracted; boundary
deltas are kept explicit and duplicates/marker terms remain intact.

This is a limited affine-fragment search, not a complete subgraph-isomorphism or
maximum-common-subgraph algorithm. It can recover fragments inside different
enclosing programs, but it cannot infer arbitrary internal wire permutations.

Main controls, zstd-22 bytes with the same `reuse` segmentation:

| Extraction | ML44 | ML65 | mdoc hash2 | mdoc signature |
|---|---:|---:|---:|---:|
| Existing cores | 889,499 | 901,065 | 99,356 | 58,669 |
| Per-output fragments | 890,408 | 903,762 | 146,982 | 62,761 |
| Per-output chunks of 8 | 890,490 | 904,478 | 153,989 | 64,145 |
| Per-output chunks of 2 | 890,796 | 904,765 | 157,128 | 66,467 |
| Windows of 32 | 916,974 | 932,586 | 212,335 | 68,875 |
| Windows of 128 | 897,366 | 911,863 | 171,452 | 59,901 |

The `reuse1` control, which also shares very short interiors, was measured for
all 20 cases. Its only improvement over the primary core candidate was ML65
gate8 at 900,791 bytes (274 bytes smaller, but larger raw and worse on the other
circuits). This is not a useful universal policy. Full results:
[fine-extraction CSV](results/first-round-slice-and-fine-sizes.csv).

On the new first-round-sliced source, per-output fragment extraction also loses:
436,283 / 442,360 bytes versus 434,599 / 439,407 with unchanged core extraction.

## mdoc and defaults

The slicing feature changes only experimental MLDSA SHAKE and its native witness
generation. mdoc does not use this module. No fine-fragment policy is installed
as a default; the existing mdoc core candidate remains unchanged (156,667-byte
combined zstd-22 archive). No new mdoc runtime measurement is claimed here.

Cargo `--all-features` enables the source experiment as well. To measure the old
MLDSA circuit with allocation tracking, select `bench-memory` explicitly instead
of using `--all-features`.

## Reproduction

Build the offline harnesses:

```sh
cargo test -p circuits-experimental --release \
  --features mldsa-first-round-slice \
  --test core_audit --test layer_templates --test template_proofs --no-run
```

For each P=1..6, export using `ORDER_DATASET=mldsa44|mldsa65`,
`MLDSA_SLICE_PERIOD=P`, and `ORDER_EXPORT_CIRCUIT=...` when running the ignored
`mldsa_core_bytes` test. Supply that file to `layer_template_order_sweep` through
`ORDER_INPUT_CIRCUIT`.

Core: `ORDER_WIRE_POLICY=whole ORDER_COMPONENTS=3 ORDER_TRAVERSALS=shape_classes
ORDER_SEGMENTS=reuse`. Morton: `ORDER_WIRE_POLICY=none ORDER_COMPONENTS=6
ORDER_TRAVERSALS=morton ORDER_SEGMENTS=standard`.

Prove the saved file with `ORDER_PROOF_CIRCUIT=...`, matching
`MLDSA_SLICE_PERIOD=P`, and `ORDER_SUMCHECK=hand` for core or
`ORDER_SUMCHECK=round` for Morton. Both the numeric and symbolic verifier use
that explicit order. No prover-side sorting, fallback schedule, new runtime
encoding or circuit-ID canonicalization was introduced.

Saved files are under `target/first-round-slice/p{1..6}/`.
Original-default Morton controls are under `target/first-round-slice/baseline/`.
