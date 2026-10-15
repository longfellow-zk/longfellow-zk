# LCT1 segmentation experiment

2026-09-12. Offline experiment on the current saved period-6 MLDSA and current
mdoc circuits. No production circuit format, scheduler, field, witness,
sumcheck implementation, or ID computation changed.

## Result

**No useful additional zstd size reduction from segmentation.** Every tested
segmented candidate is larger than the unsegmented split-stream control at
zstd-22. At zstd-16 every segmented candidate is also larger than plain LCT1.

Segmentation can substantially reduce the uncompressed representation, but
turns repetitions that zstd already compresses well into dictionaries and
reference streams that compress less well. Preserving raw records inside
segments mitigates the penalty, without producing a useful compressed-size win.

The only shared zstd-22 improvement is the control that separates metadata,
template records, and instance-map streams, without segmentation. It saves
4,492 bytes (0.62%) on MLDSA-44 and 4,353 bytes (0.57%) on MLDSA-65. On mdoc it
saves 44 bytes on hash and 223 bytes on signature. These are stream-layout
effects, not evidence in favor of segment dictionaries.

## Scope and important baseline distinction

The four inputs are the ID-checked files:

`target/traversal-circuits/{dataset}--kind_abs_lex0213_r5.lfc2`

with datasets mldsa44, mldsa65, mdoc_hash2, and mdoc_sig. LCT1 is generated afresh
from these current fixtures using the existing grouped-template encoder.
Inputs and constants, including wire 0 and its copies, remain excluded from
component connectivity. All shared-wire references remain present in maps.

These are **not the older fixtures/layouts** used in MORTON_REPORT.md. In
particular, the historical MLDSA-44 LCT1 result of 473,218 bytes at zstd-22 is not
the baseline here: current MLDSA-44 LCT1 measures 729,506 bytes. This experiment
does not reproduce or diagnose that historical-to-current gap. Comparing
segmented current files directly against 473,218 would confound segmentation
with the changed fixture/layout. Segmentation comparisons below always hold
the complete original LCT1 byte stream fixed.

The current source circuits use non-Morton storage. The historical LCT1 circuit
decoder sorts into Morton order before checking its order-sensitive circuit ID,
so it is not used for validating these current fixtures. Instead we expand the
LCT1 templates/maps once and compare every absolute term, coefficient index,
layer, and geometry/header against the source circuit. Each segmentation
variant then restores the *exact original LCT1 bytes*. We do not claim a new
production LCT1 decoder or a full original-LFC2-byte roundtrip.

## Variants

Two record pools are derived without changing their internal sequence:

- **Templates:** four-u32 records containing the already zigzag-encoded local
  coordinate deltas and the coefficient index.
- **Maps:** the original u32 varint sequence containing layer differences,
  first maps, subsequent map-difference runs, and all shared-wire references.

A small directory records each template's dimensions, instance count, and map
stream length. This lets the decoder re-interleave the streams exactly.

Tested nine segment windows: **1, 4, 8, 16, 32, 64, 128, 256, 1024**.
For each window:

1. LFC2-style symbol dictionary → segment dictionary → token stream, with the
   existing parameterized grouped-literal segmenter and frequency ordering.
2. Raw-record segment dictionary → token stream, **without** the per-record
   symbol dictionary. Raw segments are stored in first-use order to retain
   byte locality.

Each variant applies segmentation to templates only, maps only, or both.
That is **54 segmentation variants plus two controls per circuit**, or
**224 distinct circuit/encoding measurements**. Baseline/control repetitions
in the large-window follow-up reproduced identical sizes. This is a finite
heuristic experiment, not an exhaustive search over all possible segmentations
and not a runtime "try alternatives and pick" policy.

Controls are the original interleaved LCT1 and a split-stream representation
without segmentation.

## Complete file sizes, zstd-22

All values are bytes. Headers, coefficient tables, stored IDs, every template
and shared-wire mapping, dictionaries, directory entries, lengths, and token
references are included. No external compression dictionary is used.

The best-segmented column is a diagnostic minimum over the tested variants;
it is not an adopted per-circuit selection rule.

| Circuit | Plain LCT1 | Split streams, no segmentation | Best segmented | Best segmented variant |
|---|---:|---:|---:|---|
| MLDSA-44 | 729,506 | 725,014 | 730,116 | raw_maps_w1024 |
| MLDSA-65 | 764,666 | 760,313 | 764,522 | raw_maps_w1024 |
| mdoc hash, 2 attrs | 113,375 | 113,331 | 113,679 | raw_maps_w256 |
| mdoc signature | 88,876 | 88,653 | 88,777 | raw_maps_w1024 |

The 144-byte MLDSA-65 and 99-byte signature improvements over plain LCT1 are
smaller than the improvements from the no-segmentation control. Relative to
that control, adding segmentation makes both larger.

zstd-16 controls:

| Circuit | Plain LCT1 | Split streams, no segmentation |
|---|---:|---:|
| MLDSA-44 | 742,218 | 738,110 |
| MLDSA-65 | 777,232 | 772,689 |
| mdoc hash, 2 attrs | 122,137 | 121,915 |
| mdoc signature | 91,827 | 91,923 |

All segmented zstd-16 results are larger than plain LCT1; full values are in
the CSV. The split control slightly regresses signature at this level.

## Raw-size versus zstd-size tradeoff

For one fixed shared rule, LFC2-style segmentation of both pools with window 16:

| Circuit | Plain raw | Segmented raw | Plain zstd-22 | Segmented zstd-22 |
|---|---:|---:|---:|---:|
| MLDSA-44 | 8,156,804 | 2,220,293 | 729,506 | 1,141,575 |
| MLDSA-65 | 9,277,493 | 2,271,132 | 764,666 | 1,151,198 |
| mdoc hash, 2 attrs | 26,374,356 | 1,005,637 | 113,375 | 199,479 |
| mdoc signature | 956,973 | 265,448 | 88,876 | 135,109 |

Smallest raw representations in the sweep (diagnostic minima):

| Circuit | Variant | Raw bytes | zstd-22 bytes | Raw reduction vs LCT1 |
|---|---|---:|---:|---:|
| MLDSA-44 | both_w16 | 2,220,293 | 1,141,575 | 72.8% |
| MLDSA-65 | both_w16 | 2,271,132 | 1,151,198 | 75.5% |
| mdoc hash, 2 attrs | both_w64 | 775,267 | 175,315 | 97.1% |
| mdoc signature | both_w8 | 264,257 | 145,124 | 72.4% |

These are serialized representation sizes, **not measured resident-memory
requirements** of a direct LCT1 prover. The experimental decoder currently
expands back into original LCT1 bytes, so it does not retain this compact form
through proving.

## What the controls tell us

On MLDSA-44 at window 32, segmenting templates with atom IDs produces
1,082,904 bytes at zstd-22. Storing raw records in segments instead reduces that
to 821,642 bytes, but plain LCT1 is still 729,506 bytes. Removing the atom
dictionary mitigates much of the loss, not all of it.

The byte-preserving checks rule out circuit changes as the explanation.
The paired controls are consistent with dictionary IDs and segment boundaries
disrupting useful numerical/byte patterns and cross-run context. They do not
prove that every possible segmentation strategy must fail. The measured fact
is that fewer uncompressed bytes and fewer repeated record occurrences do not
translate into fewer zstd bytes for these constructions.

## Implementation and decoding measurements

`lct_segment.rs` defines an experimental `LCS1` wrapper. It contains:

- The original LCT1 header prefix and a group directory.
- A template pool and a map pool.
- A per-pool tag for plain, atom-indexed segments, or raw-record segments.
- All required dictionaries and reference streams.

The segmenter reuses the existing experimental `segment_window.rs`; synthetic
Layer objects contain symbol IDs only and are never treated as real circuits.
No runtime hash table or prover-side sorting was introduced.

For every candidate, zstd-16 decompression plus reconstruction to original LCT1
bytes was measured three times (median in the CSV). This **excludes** expansion
to circuit terms, ID verification, and any proof generation. For example,
MLDSA-44 plain zstd decode is about 2 ms, split reconstruction about 12 ms, and
the best-segmented candidate about 11 ms. These are not comparable to the
historical full-circuit LCT1 decoding times.

Both the LCT1 and LCS1 readers used here are trusted-input research code, not
hardened production decoders.

## Validation

- Every candidate restores byte-identical LCT1, including all overhead.
- Fresh LCT1 generation preserves every absolute source term/coefficient,
  duplicate, layer, geometry field, and header. Source circuit IDs are checked
  before loading and again after the experiment.
- 24 unit tests in the standalone experimental test binary passed; the large
  sweep is ignored by default. Pool tests cover both dictionary modes,
  repetitions, unmatched tails, empty streams, singletons, and u32::MAX.
- All four main sweeps and four large-window follow-ups passed.
- `cargo check --workspace --all-targets` and `git diff --check` passed.
- Strict Clippy of this test target encounters existing lint failures in the
  imported historical experiment modules; new-file diagnostics were fixed.
  No unrelated experimental cleanup or production changes were made.

## Reproduce

From the Rust workspace root, repeat for each of the four dataset names:

```sh
LCT_DATASET=mldsa44 LCT_WINDOWS=1,4,8,16,32,64,128,256,1024 LCT_ZSTD22=1 cargo test -p circuits-experimental --release --test lct_segmentation lct1_segmentation_sweep -- --ignored --nocapture --test-threads=1
```

`LCT_CIRCUIT_DIR` overrides the saved-fixture directory. By default windows are
1 through 128 from the above list; without LCT_ZSTD22 the segmented candidates
are screened at level 16 only (both controls always include level 22).

[Main sweep log](results/lct-segmentation-main.log),
[large-window follow-up](results/lct-segmentation-large.log),
[all 224 results](results/lct-segmentation.csv).

Recommendation: **do not add this segmentation for the compressed-size goal**.
Retain the experiment as evidence of the raw-size/compressed-size tradeoff.
A future direct template prover could separately evaluate whether a smaller
uncompressed representation justifies the compressed-size penalty.
