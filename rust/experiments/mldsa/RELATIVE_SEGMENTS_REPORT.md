# Relative segment references: ID-preserving LFR1 experiment

## Decision

Keep the selected MLDSA policy: period 4, special round 0, no pluckers, hand-major. Do not promote LFR1 to a production format on this evidence. It can coalesce boundary entries, but does not remove their coordinate information. The small current-MLDSA byte savings do not carry over to mdoc. All changes in this experiment are isolated to experimental code; production LFC2, readers, prover/verifier, symbolic verifier, circuit-ID computation, and slicing defaults are untouched.

## What the proposed offset means

For absolute coordinates x[j], a translated run is x'[j] = x[j] + t. Therefore its interior differences are unchanged: d'[j] = d[j] for j > 0. Only the entry difference from the previous run can change. Adding t to every delta instead adds (j+1)*t to absolute coordinates, starting from the same incoming accumulator. This is a different (affine-ramp) relation. Both relations were tested as explicit separate codec modes, never confused or silently substituted.

The existing LFC2 delta and segment dictionaries are per layer, not per chunk. A segment reference is reusable only if its entire corrected delta sequence, including coefficient indices and duplicate multiplicity, agrees exactly. No graph inference, term reordering, wire renumbering, input changes, or approximate matching is used.

The historical 466,401 / 178,492 numbers compare different traversals, not a measured partition into interior and boundary deltas. The saved shape-first control has 179,844 deltas. Instance-boundary-aware segmentation does expose many of the whole-instance deltas as entry deltas, but most of the resulting coalescing is singleton segments: their coordinates move into the three offset integers.

## Format and implementation

LFR1 is a tagged experimental container with the exact original LFC2 geometry/constant header and original 32-byte circuit ID. For each layer it stores:

1. Layer dimensions, a delta dictionary, and a dictionary of core segments (delta-index sequences).
2. References encoded as `(core_id << 1) | has_offset`; nonzero offsets add three signed ZigZag/ULEB integers. Coefficients are not offset.
3. Either references inline in execution order, or a deduplicated reference table plus ordinary integer execution tokens.

The encoder groups segments by exact equality after removing their entry coordinates (or the common delta shift in the affine control). It then uses an actual first representative, rather than an artificial zero-origin core. Unshared segments and uses identical to the representative have no offset payload. Dictionary IDs are frequency-ranked for the indices actually written; an ordinary-LFC2 delta-ranking control is reported separately. All framing, constants, dictionary indices, reference tags, offsets, execution tokens, and the ID are counted in raw and compressed sizes.

The compatibility decoder expands references into ordinary LFC2 dictionaries, not a flat array of all executed terms. The current prover still consumes its existing compact Layer representation. This prototype saves serialized bytes only, not the expanded delta dictionary's in-memory space. It uses offline/load-time hash tables; none is added to proving or verification. A future direct LFR1 layer iterator would require integration and hardening and has not been implemented or performance-claimed here.

## Current circuits

Exact bytes, standalone zstd level 22. MLDSA uses the measured whole / shape_classes / reuse LFC2 layout at the selected slicing configuration. mdoc uses the saved two-attribute hash and signature controls. These are individual circuit sizes, not a sum intended to predict an archive's compressed size.

| Circuit | LFC2 raw | LFC2 z22 | Relative inline raw | Relative inline z22 | Relative pooled raw | Relative pooled z22 |
|---|---:|---:|---:|---:|---:|---:|
| mldsa44 | 1,642,397 | 367,947 | 1,627,148 | 360,045 | 1,627,743 | 364,199 |
| mldsa65 | 1,805,553 | 377,432 | 1,784,906 | 369,313 | 1,785,773 | 373,572 |
| mdoc_hash2 | 548,467 | 100,969 | 555,212 | 103,099 | 546,768 | 104,121 |
| mdoc_sig | 222,143 | 63,398 | 221,786 | 64,487 | 226,661 | 64,826 |

### What actually coalesces

`Boundary-only` counts distinct deltas appearing at existing segment starts and nowhere in interiors. `Merged multi-term segments` excludes the trivial sharing of single-term segments with equal coefficients.

| Circuit | Original deltas | Boundary-only | Relative core deltas | Merged multi-term segments | Pooled offset bytes | Inline offset bytes |
|---|---:|---:|---:|---:|---:|---:|
| mldsa44 | 49,849 | 2,120 | 48,739 | 16 | 5,765 | 11,384 |
| mldsa65 | 51,169 | 2,261 | 49,936 | 152 | 6,605 | 12,114 |
| mdoc_hash2 | 18,210 | 315 | 18,203 | 23 | 112 | 777 |
| mdoc_sig | 12,708 | 242 | 12,702 | 6 | 40 | 66 |

### No-format-change control

Reindex the original delta dictionary by serialized-reference frequency, with no new reference encoding and no ID change:

| Circuit | Original z22 | Reindexed LFC2 raw | Reindexed LFC2 z22 |
|---|---:|---:|---:|
| mldsa44 | 367,947 | 1,621,858 | 364,687 |
| mldsa65 | 377,432 | 1,783,631 | 371,132 |
| mdoc_hash2 | 100,969 | 537,633 | 101,670 |
| mdoc_sig | 63,398 | 221,059 | 63,476 |

## Historical whole-instance hypothesis

These controls retain period 6, the historical 24/4-byte field encoding and original IDs. A read-only historical serialization adapter recomputes and checks the original IDs; no old file is reinterpreted as an 18-byte field circuit.

| Traversal / segmentation | Original deltas | Boundary-only | Relative core deltas | Original raw / z22 | Inline relative raw / z22 | Pooled relative raw / z22 |
|---|---:|---:|---:|---:|---:|---:|
| whole | 466,401 | 13,367 | 466,182 | 6,393,561 / 1,932,323 | 6,360,808 / 1,978,799 | 6,454,800 / 2,098,113 |
| shape | 179,844 | 3,986 | 179,823 | 3,220,462 / 1,023,325 | 3,215,857 / 1,041,922 | 3,258,892 / 1,063,191 |
| boundary32 | 466,401 | 278,171 | 195,791 | 6,878,534 / 2,105,889 | 5,414,424 / 1,518,288 | 5,970,767 / 1,932,098 |
| boundary128 | 466,401 | 273,674 | 196,909 | 7,460,846 / 1,958,648 | 5,618,511 / 1,572,758 | 6,160,271 / 1,959,327 |

The boundary-aware files have the exact same term order and ID as the whole-instance file; only their segmentation differs. They establish that boundary/jump entries are a real contributor. With boundary32 and inline references, the historical whole traversal improves from 1,932,323 to 1,518,288 compressed bytes (or from 2,105,889 for its boundary32 LFC2 representation). This is a real win, but still worse than the historical shape-first control at 1,023,325 bytes. The reference overhead is proportional to the number of distinct segment references, not eight SHAKE permutations or a small number of complete template instances:

| Boundary segmentation | Original segments | Core segments | Pooled references | Merged multi-term segments | Offset + reference-tag bytes | Token bytes |
|---|---:|---:|---:|---:|---:|---:|
| boundary32 | 314,474 | 43,794 | 314,474 | 4,798 | 2,224,114 | 1,244,684 |
| boundary128 | 297,593 | 28,084 | 297,593 | 3,627 | 2,181,069 | 1,018,465 |

A 3-integer reference is sufficient for a genuinely translated segment, but it is not an encoding of an arbitrary input/output map. Fixed inputs, constant wires, and non-translation instance mappings can alter interior differences and force additional segments. Thus the proposed ~200 bytes per complete instance cannot be assumed from delta-table cardinalities.

## Sweep coverage and verification

112 variants: first-delta and all-delta corrections; inline and pooled references; existing segmentation and fixed stream chunks of 8/32/128 where applicable. The exact same terms, coordinates, input hands, coefficients, multiplicities, layer dimensions, constants, and ID are checked after every decode. Four unit tests cover translation versus affine behavior, shared-port/coefficient mismatches, negatives, duplicates, empty segments, truncation, invalid indices and mode tags. Current source-circuit controls (before the offline whole/shape_classes/reuse ordering) are also included in the CSV.

### Best compressed candidate observed per fixture (diagnostic, not an adaptive policy)

| Fixture | Variant | Raw | z22 |
|---|---|---:|---:|
| mldsa44 | all-inline-w0 | 1,642,553 | 359,106 |
| mldsa44_source | all-inline-w0 | 1,757,041 | 473,706 |
| mldsa65 | all-inline-w0 | 1,810,378 | 368,875 |
| mldsa65_source | all-inline-w0 | 2,001,738 | 502,014 |
| mdoc_hash2 | all-inline-w0 | 555,213 | 103,080 |
| mdoc_sig | all-inline-w128 | 276,889 | 60,915 |
| historical44_whole | first-inline-w0 | 6,360,808 | 1,978,799 |
| historical44_shape | all-inline-w128 | 5,669,699 | 1,030,519 |
| historical44_boundary32 | first-inline-w0 | 5,414,424 | 1,518,288 |
| historical44_boundary128 | first-inline-w0 | 5,618,511 | 1,572,758 |

## Decoder and proof checks

Size-sweep jobs overlap; encode/decode timing columns in the sweep CSV are diagnostics only. Separate serial loader measurements below use seven repetitions, median, excluding circuit-ID hashing for both paths. The relative measurement includes reference expansion, LFC2 serialization, and the normal reader; it measures the compatibility adapter, not an optimized direct LFR1 decoder.

| Circuit | LFC2 decode ms | Relative adapter + decode ms |
|---|---:|---:|
| mldsa44 | 2.270 | 17.952 |
| mldsa65 | 2.575 | 19.346 |
| mdoc_hash2 | 1.058 | 5.760 |
| mdoc_sig | 0.427 | 3.298 |

Both selected MLDSA circuits were proved again after decoding pooled first-delta references. The harness asserted byte-for-byte equality against the saved p4-b0-r1 proof, then parsed and verified it. Proof sizes remain 218,708 / 227,852 bytes. These one-flow correctness checks are not a replacement for the earlier five-run runtime benchmarks. No mdoc end-to-end proof was rerun in this experiment; its exact streams and computed circuit IDs were verified.

## Reproduction

```sh
cargo test --release -p circuits-experimental --test relative_segments -- --nocapture
python3 experiments/mldsa/run_relative_segments.py
python3 experiments/mldsa/summarize_relative_segments.py
```

[All size results](results/relative-segments.csv) · [Codec](relative_segments.rs) · [Runner](run_relative_segments.py)

Complete LFR1/zstd artifacts, decoded controls, and logs are in `target/relative-segments-representative`. The earlier zero-base engineering controls are retained separately in `target/relative-segments-final` and `target/relative-segments-ranked`; they are not the results reported above.
