# Shared template cores plus residual terms, in ordinary LFC2

2026-09-12, dirty `rust` worktree based on
`fa578cc5bb055d72df379dc195393ea2f124788e`, Ryzen 9950X, Rust 1.97.1,
release/native. Saved current MLDSA-44/65 and two-attribute mdoc circuits.

## Outcome

Implemented the user's proposed alternative to patched templates: keep exactly
shareable terms in a template core and emit all exceptions separately. This
requires **no new format, runtime maps, patch opcodes, sorting or hash tables**.
All files are ordinary segmented LFC2, directly consumed by hand-major proving.

The main comparison keeps the preceding experiment's whole-template wire layout
and its `reuse` segmentation rule fixed. Only the core/residual traversal changes.
The same rule is applied to every circuit; production defaults remain unchanged.

| zstd-22 bytes | Current default | Previous wire/template candidate | Core/residual candidate |
|---|---:|---:|---:|
| MLDSA-44 | 959,815 | 939,456 | 889,499 |
| MLDSA-65 | 989,616 | 953,232 | 901,065 |
| mdoc combined archive | 162,101 | 156,579 | 156,667 |

This saves a further **5.3% / 5.5%** over the preceding MLDSA candidate, or
**7.3% / 8.9%** versus the unchanged default. The mdoc archive is essentially
unchanged from the previous candidate: **88 bytes larger**, despite slightly
smaller standalone compressed hash and signature circuits. It remains 3.4%
below the current default. The strict 500,000-byte MLDSA goal is still unmet.

## Exact algorithm

The decomposition splits **terms**, not the actual circuit wires. In particular,
different summands contributing to one gate may be in a core and the residual
stream. Nothing is deleted, duplicated or moved across layers.

For each shape and existing exact template family:

1. Expand the instance maps offline into absolute term coordinates. For each
   corresponding local term `j`, form the vector of coordinate offsets from
   instance zero to every other instance:
   `signature(j) = [(g_i-g_0, h0_i-h0_0, h1_i-h1_0) for each i]`.
2. Terms with the same signature form a translated subcore. This equality is
   checked across **every instance**, not just two samples, and includes the
   actual canonicalized input hands. Coefficients already match by construction.
   A term whose shape differs across instances is not put into a shared core.
3. Preserve local term order within each subcore. Emit its instances consecutively.
   Their interior delta tuples are identical; an explicit assertion checks that.
   Only the boundary jump differs between instances.
4. Collect all remaining terms, including singleton groups, into the residual
   stream for that shape and layer. Sort residuals by descending output,
   descending second input, ascending first input, then coefficient index.
5. Apply ordinary absolute-coordinate differencing continuously across the whole
   traversal. Store repeated exact interiors using the preceding experiment's
   LFC2 segmentation rule. Keep the boundary delta outside the shared interior.

The outer order remains constant / linear / square / product. Constant-one
copies are recognized by value propagation. Original inputs and final outputs
remain fixed; the internal numbering is exactly the preceding whole-template
policy. Wires, term counts, geometry, witnesses, period 6, SHAKE basis, field
arithmetic and CRT are unchanged.

This is not approximate arithmetic or approximate decoding. "Approximate"
describes the initial template match; the stored cores and residuals reconstruct
the original term multiset exactly under the checked internal-wire bijections.

## One core versus several subcores

Two explicit controls were tested:

- `shape_core`: retain the largest translation class for each shape/family,
  with first occurrence breaking ties; all other terms become residuals.
- `shape_classes`: retain every translation class with at least two terms;
  singleton classes become residuals. This is the main candidate, because it
  retains additional independently shareable runs instead of discarding them.

Both use deterministic structural rules, not trial encodings or per-circuit
compressed-size selection. The minimum of two terms means that a core has an
interior delta to share; a one-term instance has only a boundary placement.

With the previous `reuse` segmenter held fixed:

| zstd-22 bytes | Largest core | Several subcores |
|---|---:|---:|
| MLDSA-44 | 900,956 | 889,499 |
| MLDSA-65 | 914,088 | 901,065 |
| mdoc hash2 | 99,361 | 99,356 |
| mdoc signature | 58,786 | 58,669 |

The several-subcore candidate partitions the expanded terms as follows:

| Circuit | Shared-core terms | Residual terms | Total terms |
|---|---:|---:|---:|
| MLDSA-44 | 5,497,007 | 1,083,780 | 6,580,787 |
| MLDSA-65 | 6,685,110 | 1,268,878 | 7,953,988 |
| mdoc hash2 | 1,722 | 6,393,113 | 6,394,835 |
| mdoc signature | 96,972 | 179,509 | 276,481 |

This template decomposition finds substantial repeated cores in MLDSA, but
almost none in mdoc hash2. It is not a new search for arbitrary repeated fragments
inside the large unmatched components. The mdoc residual stream still benefits
from ordinary LFC2 segmentation and zstd.

MLDSA-44's distinct deltas fall from 177,498 in the preceding wire candidate to
171,820; MLDSA-65 falls from 174,758 to 166,683. Those dictionaries remain large.
The first input-consuming layer now has 1,961,824 / 3,117,712 shared-core terms
and 306,045 / 364,792 residual terms (44/65). Fixed original inputs do not prevent
all sharing: different regularly translated input regions can form different
subcores without renaming those inputs.

## Raw size and segmentation controls

All standalone sizes below include ordinary LFC2 headers, constants, deltas,
segments and tokens. There are no hidden mapping or patch bytes.

| Main candidate | Raw | zstd-16 | zstd-22 |
|---|---:|---:|---:|
| MLDSA-44 | 2,628,172 | 927,206 | 889,499 |
| MLDSA-65 | 2,761,654 | 938,610 | 901,065 |
| mdoc hash2 | 543,913 | 111,080 | 99,356 |
| mdoc signature | 244,943 | 58,818 | 58,669 |
| Combined mdoc LFA2 archive | 789,028 | 177,698 | 156,667 |

Standalone files use bulk zstd; the mdoc archive uses streaming zstd. The archive
row excludes the benchmark container's 32-byte trusted-ID prefix. Compressed
standalone sizes cannot be summed to predict the archive size.

MLDSA-44/65 raw sizes improve 1.6% / 4.7% over the current default. The mdoc archive
is 2.4% larger raw than default and 0.2% larger than the preceding wire candidate.

`reuse` shares repeated interiors of at least 32 terms, retaining the existing
segmentation outside them. An additional `reuse1` control shares interiors of
any positive length. With several subcores it gives:

| Circuit | Raw with reuse1 | z22 with reuse1 |
|---|---:|---:|
| MLDSA-44 | 2,698,651 | 888,153 |
| MLDSA-65 | 2,848,231 | 901,013 |
| mdoc hash2 | 543,096 | 99,381 |
| mdoc signature | 244,868 | 58,837 |
| Combined mdoc archive | 788,136 | 156,846 |

Sharing very short interiors adds many segment references and saves little zstd
space: MLDSA-44 gains only 1,346 compressed bytes but adds 70,479 raw bytes versus
the main candidate; MLDSA-65 gains 52 compressed bytes but adds 86,577 raw bytes.
The main comparison therefore retains the **unchanged preceding segmentation
rule**, rather than presenting tiny-core sharing as a new universal improvement.

Using only the ordinary segmenter after extraction gives MLDSA-44/65 raw sizes
2,374,027 / 2,452,915 and z22 sizes 918,761 / 927,506. This is a useful raw-size
trade-off; it is not automatically chosen per circuit.

Without template-driven wire renaming, the several-subcore/reuse1 control gives
922,110 / 932,675 bytes for MLDSA, 102,631 for mdoc hash2 and 57,711 for mdoc
signature. Thus a circuit-specific mixture could improve individual entries,
but no such mixture is used by the proposed common policy.

All 32 new candidates, including LFC1 and dictionary/segment/token counts:
[results/template-core-sizes.csv](results/template-core-sizes.csv).
Per-layer core/residual coverage:
[results/template-core-coverage.csv](results/template-core-coverage.csv).
Size-sweep build/decode times are diagnostics, not isolated benchmarks.

## Proof performance

Five sequential repetitions per profile, same default-allocator release binary,
no overlapping size sweeps or builds. Medians:

| Circuit | Policy | Prover ms | Verifier ms | Load + ID ms | Proof bytes |
|---|---|---:|---:|---:|---:|
| mldsa44 | Current default | 1069.7 | 655.1 | 178.0 | 665416 |
| mldsa44 | Shared cores + residuals | 1076.4 | 659.1 | 176.8 | 665544 |
| mldsa44 | Also share tiny interiors | 1092.2 | 657.7 | 176.4 | 665544 |
| mldsa65 | Current default | 1213.9 | 737.4 | 215.1 | 719368 |
| mldsa65 | Shared cores + residuals | 1220.4 | 742.3 | 214.3 | 719176 |
| mldsa65 | Also share tiny interiors | 1217.9 | 740.3 | 212.9 | 719176 |
| mdoc | Current default | 353.0 | 184.9 | included | 344236 |
| mdoc | Shared cores + residuals | 352.4 | 187.4 | included | 343436 |
| mdoc | Also share tiny interiors | 346.3 | 188.2 | included | 343436 |

MLDSA prover is commit + prove, excluding load/ID, input preparation and proof
serialization/deserialization. Its verifier timer is the core verification after
proof reading. Load includes one ID check; there is an additional untimed check
before proving. The mdoc timer is full application proving/verification including
decompression and decode; its trusted loader does not recompute circuit IDs.
Use this paired run, rather than comparing small differences across older reports.
There is no material speed improvement established; mdoc remains below 380 ms on
this fixture. No runtime arithmetic was changed in this experiment.

All timed proofs were serialized, decoded and verified. The two segmentation
profiles produced byte-identical deterministic proofs of the same new traversal.
Core/residual reordering changes the existing order-sensitive circuit ID and
transcript challenges, but not proof geometry or the ID algorithm. The small
proof-size differences are transcript-dependent Merkle multiproof sharing, not
new witnesses. MLDSA-44 is 128 bytes larger than default in this deterministic
sample; MLDSA-65 is 192 bytes smaller and mdoc is 800 bytes smaller. No guarantee
of smaller proof bytes for every transcript is implied.

Raw samples: [results/template-core-timings.csv](results/template-core-timings.csv).

## Actual memory

Separate allocation-tracking build, one proof/verification per fresh process.
`/usr/bin/time -v` measures process high-water RSS; live-allocation tracking
measures phase heap peaks. Circuit compilation and archive compression happen
outside the measured process. Timing runs do not enable allocation tracking.

| Circuit | Policy | Peak RSS MiB | Prover live-heap peak MiB | Verifier live-heap peak MiB |
|---|---|---:|---:|---:|
| mdoc | Current default | 102.42 | 92.48 | 38.07 |
| mdoc | Shared cores + residuals | 102.49 | 92.56 | 38.14 |
| mdoc | Also share tiny interiors | 102.08 | 92.56 | 38.14 |
| mldsa44 | Current default | 121.87 | 117.99 | 33.41 |
| mldsa44 | Shared cores + residuals | 120.77 | 117.40 | 32.81 |
| mldsa44 | Also share tiny interiors | 121.10 | 117.67 | 33.09 |
| mldsa65 | Current default | 131.66 | 129.49 | 40.12 |
| mldsa65 | Shared cores + residuals | 130.57 | 128.67 | 39.30 |
| mldsa65 | Also share tiny interiors | 131.05 | 129.00 | 39.63 |

RSS is not a verifier-only peak. Tracked heap excludes stack/code pages and freed
memory retained by the allocator. MLDSA verification retains the benchmark's
prepared input vector. Phase-added sumcheck/prover scratch is unchanged; the
small heap reduction comes from the resident ordinary-LFC2 representation.
Exact counts: [results/template-core-memory.csv](results/template-core-memory.csv).

## Reproduction

```sh
cargo test --release -p circuits-experimental --test layer_templates --no-run
ORDER_DATASET=mldsa44 ORDER_WIRE_POLICY=whole ORDER_COMPONENTS=3 \
ORDER_TRAVERSALS=shape_core,shape_classes ORDER_SEGMENTS=standard,reuse,reuse1 \
ORDER_SAVE_DIR=target/template-core-lfc2 \
  cargo test --release -p circuits-experimental --test layer_templates \
  layer_template_order_sweep -- --ignored --nocapture
```

Use `ORDER_WIRE_POLICY=none` for the no-renaming control. All original inputs are
fixed under both settings. The main saved file is
`DATASET-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2`.

Saved-circuit proof harness and measurement boundaries are unchanged from
[TEMPLATE_WIRE_LFC2_REPORT.md](TEMPLATE_WIRE_LFC2_REPORT.md).

## Validation completed

- All 32 new candidates pass exact term-multiset, traversal, LFC2 serialization
  and circuit-ID round-trip checks. Each shared core's interior deltas are
  explicitly compared across every instance. The preceding wire bijection and
  fixed original input/output checks remain active.
- 45 timed and 9 fresh-memory proof/verification flows pass on MLDSA-44,
  MLDSA-65 and the current two-attribute mdoc pair. The two new segmentation
  profiles give identical deterministic proofs for each circuit.
- `cargo test --release -p circuits-experimental --test layer_templates --test template_proofs`:
  38 non-ignored tests pass. New tests cover irregular wires moved to residuals,
  duplicated terms and assertion markers, shape disagreements across instances,
  multiple disjoint translation classes, and sharing short interiors.
- `cargo test --release -p core-proto -p runtime-sumcheck -p runtime-zk`: passes.
- `cargo check --workspace --all-targets`: passes without warnings.
- `git diff --check`: passes. No production format, compiler default, prover or
  verifier changes were made for this experiment; unrelated worktree changes remain.
