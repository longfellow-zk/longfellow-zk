# Scheduling and segmentation sweep: MLDSA and mdoc

2026-09-13. All code and measurements are experimental. Production scheduler,
formats, prover/verifier, protocol defaults, and C++ sources are unchanged by
this sweep. Release/native Rust builds on the Ryzen 9950X.

## Outcome

The new numbering policies did not improve the selected compressed MLDSA layout.
The useful improvement came from **retaining exact template-interior reuse and
changing only segmentation outside those interiors**.

Recommend the simple `whole / shape_classes / reuse_window_64` candidate for a
future integration: it improves zstd-16 and zstd-22 for both MLDSA circuits and
the combined mdoc archive, without a new format or runtime behavior. It is not
installed as the default. More elaborate content-defined variants shave off a
few additional KB but have substantially larger raw MLDSA representations.

Exact bytes, standalone bulk zstd-22 for MLDSA and jointly streaming-compressed
LFA2 for the two-attribute mdoc archive:

| Shared policy | MLDSA-44 | MLDSA-65 | mdoc archive |
|---|---:|---:|---:|
| Existing whole / shape_classes / reuse (32-term base) | 367,947 | 377,432 | 156,667 |
| Same traversal, stock 64-term segmentation without template reuse | 379,389 | 386,290 | 152,764 |
| **Reuse interiors + 64-term stock base** | **364,288** | **373,916** | **150,818** |
| Reuse interiors + 128-term stock base | 363,854 | 371,373 | 149,458 |
| Reuse interiors + content-defined 128 base | 363,275 | 369,259 | **146,340** |
| Reuse interiors + content-defined 64 stored-ranking base | **362,947** | **368,416** | 149,386 |

The last row is the lowest compressed MLDSA size observed in this experiment;
the preceding row is the lowest combined mdoc archive. These are fixed shared
rules, not a runtime or compiler tournament. No policy-specific application
name tests are used. The per-circuit minima are diagnostics, not an adopted
mix-and-match scheduler.

Corresponding raw LFC2/LFA2 bytes:

| Shared policy | MLDSA-44 | MLDSA-65 | mdoc archive |
|---|---:|---:|---:|
| Existing reuse | 1,642,397 | 1,805,553 | 789,028 |
| Stock 64, without reuse | **1,303,819** | **1,381,901** | 714,779 |
| Reuse + stock 64 | 1,704,073 | 1,871,319 | 743,421 |
| Reuse + stock 128 | 1,744,992 | 1,893,342 | 781,729 |
| Reuse + content-defined 128 | 2,030,895 | 2,205,120 | 1,009,975 |
| Reuse + content-defined 64 stored-ranking base | 1,841,003 | 2,037,884 | 764,931 |

Stock 64 without reuse is the raw-MLDSA minimum of the measured matrix. The
recommended combination reduces compressed MLDSA by about 1%, and mdoc by 3.7%,
while increasing raw MLDSA 3.6–3.8% and decreasing raw mdoc 5.8%. The absolute
compressed MLDSA minima save 1.4% / 2.4% but increase raw MLDSA 12.1% / 12.9%.
Raw serialized bytes are not a claim about measured process RSS.

The recommended candidate also improves zstd-16: MLDSA 394,859 / 403,606 becomes
393,476 / 402,364, and mdoc 177,698 becomes 171,782. The stored-ranking CDC64
variant slightly regresses MLDSA-65 at zstd-16 (403,752 versus 403,606); this is
another reason not to select it solely from the zstd-22 minimum.

## Scope and complete matrix

The main matrix is **6 numbering rules × 4 traversals × 12 segmenters × 4
circuits = 1,152 measurements**, plus **32 targeted refinement measurements**.
All 1,184 have raw, zstd-16, and zstd-22 sizes. Every one of the 296 shared
profiles also has an actual jointly compressed mdoc archive, not an estimated
sum of standalone sizes. A finite heuristic matrix is not an exhaustive search
of all possible wire permutations or segmentations.

Fixtures are the saved selected MLDSA-44 and MLDSA-65 circuits (period 4, special
round 0, no pluckers, direct XOR-basis witnesses, boundary=ninput, 18/3-byte field
serialization), and mdoc v8 signature/hash with two attributes. No input or final
output is renamed; no wires, terms, witnesses, constraints, or layers are added.

| Circuit | Wires including inputs/outputs | Terms | Layers |
|---|---:|---:|---:|
| MLDSA-44 | 3,613,574 | 6,691,580 | 24 |
| MLDSA-65 | 3,791,554 | 8,064,583 | 24 |
| mdoc signature | 183,618 | 276,481 | 21 |
| mdoc hash2 | 3,473,933 | 6,394,835 | 20 |

Numbering:

- `none`: retain original compiler wire IDs.
- `whole`: exact whole-component families, then instances, then local wires.
- `layer`: independently group exact layer programs.
- `role`: exact whole-component families, then local role, then instance.
- `role4`, `role16`: tile local roles in groups of 4 or 16 before visiting instances.

Original inputs and proven constants, including all copies of one, do not connect
the component families. All internal maps are dense bijections checked by exact
inverse renaming. Family/instance order is deterministic minimum original ID;
hash-table iteration does not determine numbering.

Traversals:

- `shape`: constant/linear/square/product, g descending, h1 descending, h0 ascending.
- `shape_classes`: the selected exact translated subcores plus residuals.
- `shape_terms`: within shape/template families, interleave corresponding terms
  across instances rather than emit complete instances.
- `morton`: global absolute Morton input-pair order after numbering.

Segmenters, all ordinary LFC2:

- Stock grouped-literal macro segmentation at widths 16, 32, 64, 128. The actual
  code discovers candidates at aligned positions and requires at least two uses.
- Exact template-interior reuse with stock-32 outside shared interiors.
- Fixed chunks of 32 or 128 delta indices.
- Content-defined segmentation targeting 32 or 128 terms: rolling eight-symbol
  content hash, minimum width/4, maximum 4×width; anchors use delta values rather
  than frequency-assigned delta IDs. These widths are targets, not exact means.
- All-position macro discovery at widths 32 and 64, with exact matching after
  hash lookup, then greedy parsing and grouped literals.
- Content-defined 64 with delta ranking by references in stored segment bodies
  instead of expanded execution frequency.

The follow-up keeps `whole / shape_classes` fixed and varies the base segmenter
under exact-interior reuse: stock 16/32/64/128, CDC32/128, stored-ranking CDC64,
plus an ordinary CDC64 control. Stock-32 reproduces the selected files byte for
byte. The reuse routine still performs its normal final frequency reranking;
the stored-ranking label describes the base, not a guarantee that every final
dictionary is stored-reference ranked. Its effect includes tie order.

## What the experiments explain

1. **Numbering and traversal remain coupled.** Pure role-major and tiled-role
   policies did not beat whole-instance numbering. For MLDSA-44 with the same
   shape_classes/reuse policy, pure role-major gives 400,463 bytes versus 367,947;
   its delta count is 56,199 versus 49,849. The structural diagnostic counts
   351,312 translated internal-input maps under role numbering versus 356,607
   under whole numbering, across the same 356,607 compared blocks.
2. A reason role numbering is not automatically better is visible in the layout
   formula: the distance between local roles equals the number of instances in
   that whole-component family. Different family multiplicities therefore give
   different local strides, even when some layer programs match. Whole-instance
   numbering keeps local-role stride independent of family multiplicity. This
   is a structural explanation consistent with the diagnostic, not a measured
   attribution of every lost byte to that cause.
3. **More discovered matches can encode worse.** On selected MLDSA-44, all-position
   32-term discovery stores 1,395,544 segment entries versus 525,050 for stock-32;
   the delta count remains 49,849. It produces 44,292 segments versus 17,247.
   Greedily accepting more repeated short windows can disrupt the useful parse.
4. **A large fraction of the remaining choice is segmentation, not new deltas.**
   All refinement variants preserve the exact delta stream, counts, traversal,
   and circuit ID. Reuse protects long MLDSA runs while a different residual
   segmenter improves dictionary/token encoding elsewhere. The mdoc hash has
   little reusable template interior, so it primarily benefits from the base
   segmenter. This motivates the compositional policy without branching on the
   circuit name or trying several encodings at runtime.

## Morton-compatible results

Alternative segmentation helps, but does not bring a no-sort round-major MLDSA
circuit near 500 KB. A shared Morton policy that also preserves/improves the
original Morton mdoc archive is original numbering plus CDC128:

| Policy | MLDSA-44 z22 | MLDSA-65 z22 | mdoc archive z22 |
|---|---:|---:|---:|
| Original numbering, Morton, stock-32 | 2,490,683 | 2,509,490 | 299,804 |
| Original numbering, Morton, CDC128 | 2,328,656 | 2,357,975 | 272,174 |
| Role numbering, Morton, CDC128 | 1,970,177 | 2,187,191 | 407,432 |

The last row improves MLDSA further but regresses mdoc, so it is not a shared
replacement. All non-Morton traversal candidates are for hand-major proving.

## Verification and limitations

- 44 release unit tests passed, covering exact segment reconstruction, shifted
  repeated runs, empty streams, template correctness, and inverse wire maps.
- Every main/refinement candidate passed ID-checked LFC2 decoding, byte-for-byte
  LFC2 serialization roundtrip, exact expanded delta comparison, and geometry
  checks. Every layout passed exact term-multiset validation; internal renaming
  additionally passed inverse-map checks with fixed inputs and final outputs.
- All 296 mdoc archives were constructed from ID-checked constituent files.
- Four leading refinements each passed full MLDSA-44, MLDSA-65, and mdoc proving,
  proof serialization/parsing, and verification, with byte-identical proofs
  compared to the saved selected baseline. Proof sizes remain 218,708 / 227,852
  for MLDSA and 343,436 for this deterministic mdoc fixture.
- Representative role-numbered hand-major and Morton circuits also passed full
  proofs for both MLDSA variants and mdoc (six additional flows). MLDSA Morton
  proofs use round-major; mdoc v8 application proofs remain hand-major. Actual
  no-sort round-major folding was independently checked on every layer of all
  four role/Morton circuits against direct equality-weighted evaluation.
- Two additional stock-64-without-reuse MLDSA proofs matched the saved proof bytes.
  In total, 20 end-to-end correctness flows were run for this sweep. Not every
  one of the 1,184 size candidates received a full proof; all received the exact
  preservation and decoder checks above.
- Timing columns are offline diagnostics from concurrent jobs. Proof checks are
  single-flow correctness checks, not a new controlled speed or peak-RSS benchmark.
- Both zstd-16 and zstd-22 use libzstd bulk compression for individual circuits;
  the Python level-22 path was cross-checked against Rust on the selected file
  (exactly 367,947 bytes). mdoc uses the production streaming archive compressor.
  Archive sizes exclude the benchmark-only 32-byte trusted-ID prefix.
- No claim is made that the finite search proves an optimal layout, or that every
  possible partial-template matcher, bidirectional graph canonicalization, or
  source-level transformation was tested.

## Artifacts and reproduction

[Main 1,152 measurements](results/scheduling-segmentation-main.csv),
[288 shared policies and paired archives](results/scheduling-segmentation-shared.csv),
[32 refinement measurements](results/scheduling-segmentation-refine.csv), and
[eight shared refinements](results/scheduling-segmentation-refine-shared.csv).

The runner is `run_scheduling_sweep.py` (phases screen, summary, compress).
`summarize_scheduling_sweep.py` builds archives and final tables.
`run_segmentation_refinement.py` runs the targeted follow-up;
`validate_scheduling_sweep.py` runs representative end-to-end checks.

Build the three release test binaries:

```sh
cargo test --release -p circuits-experimental --features mldsa-slicing-experiment --test scheduling_sweep --test template_proofs --test morton_folds --no-run
```

The workspace supplies native CPU optimization. Use the binary paths printed by
Cargo. The main runner can receive `--binary`; the small fixed-fixture refinement
and validation runners record the release binary names used here.

Main artifacts, executable hash, saved v1 executable, all LFC2 files, all archives,
unit-test logs, and proof-validation logs are under `target/scheduling-segmentation-v1`.
Refinement artifacts are under `target/scheduling-segmentation-refine`. The
saved v1 executable is `scheduling_sweep_v1`; the later source includes additional
base-segmenter choices, so do not resume a v1 root with a differently hashed binary.
