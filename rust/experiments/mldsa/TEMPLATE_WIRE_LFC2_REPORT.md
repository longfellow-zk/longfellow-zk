# Template-driven wire numbering for ordinary LFC2

2026-09-12, dirty `rust` worktree based on
`fa578cc5bb055d72df379dc195393ea2f124788e`, Ryzen 9950X, Rust 1.97.1,
release/native. Saved current circuits; no clean-HEAD or C++ comparison.

## Result and scope

Implemented an offline wire-numbering experiment, not a new format. A single
**whole-template-family layout + shape-first template traversal + exact-interior
reuse** rule improves zstd-22 size on MLDSA-44, MLDSA-65 and the current
two-attribute mdoc pair. The gains are modest, not close to the 500,000-byte
MLDSA target. Raw size is mixed; no production default is changed.

Original inputs (public, private, and wire zero) and final outputs are fixed.
Every internal layer map is a dense bijection, applied to both producers and
consumers. No wires, padding, witnesses, constraints, terms or layers are added.
Coefficient tables, period 6, XOR-basis SHAKE, field arithmetic and CRT are unchanged.
Input hands are re-canonicalized by min/max after renaming; the inverse check
therefore compares exact term multisets with commutative input normalization,
not merely sampled evaluations or equal wire counts.

The saved circuit is directly consumed as standard segmented LFC2. There are no
runtime maps, expansions, sorts or hash tables. LTP remains abandoned. These
non-Morton traversals are for the existing dense hand-major protocol, not the
round-major consumer's Morton contract.

## Single candidate policy

1. Discover global connected components with original inputs and all proven
   constants, including copies of one, excluded from connectivity.
2. Match complete component DAGs exactly: local layer programs, port types and
   constant values, and each internal input's rank in the preceding output map.
   This is stronger than independently matching per-layer shapes.
3. At each internal depth, place constant ports first, grouped by value. Then
   lay out template families, their instances, and local output wires. Families
   and instances are ordered by their minimum original global wire ID; no hash
   iteration controls numbering. Unmatched components are singleton families.
4. Apply the same map to that depth's output coordinates and the next layer's
   input coordinates. Keep the original input and final output maps as identity.
5. Discover layer templates on the renamed circuit and traverse
   **shape / template / instance / local term**. Shapes are constant, linear,
   square and product, recognizing proven copies of one.
6. Compute ordinary absolute-coordinate deltas, continuously across boundaries.
   Start from the existing segmentation. If a template interior of at least 32
   terms occurs exactly more than once, store it as one reusable segment; retain
   ordinary segmentation outside those spans, splitting only at span boundaries.
   The first context-dependent delta stays outside the shared body. Reindex delta
   and segment dictionaries by frequency as usual.

The 32-term minimum is one chunk of the existing segmenter, not a component-size
majority threshold or a circuit-specific selector. The implementation does not
encode multiple candidates and choose a winner. Explicit experiment selectors
are used only to establish the effects below.

## Serialized sizes

Bytes, standalone bulk zstd. All headers, constants, deltas, segment dictionaries
and tokens are counted. No omitted mapping overhead: maps exist offline only.

| Circuit | Current raw | Candidate raw | Current z16 | Candidate z16 | Current z22 | Candidate z22 |
|---|---:|---:|---:|---:|---:|---:|
| MLDSA-44 | 2,670,639 | 2,695,301 | 997,383 | 981,580 | 959,815 | 939,456 |
| MLDSA-65 | 2,896,804 | 2,884,432 | 1,031,363 | 998,351 | 989,616 | 953,232 |
| mdoc hash2 | 548,467 | 546,463 | 112,990 | 111,181 | 100,969 | 99,594 |
| mdoc signature | 222,143 | 240,646 | 63,443 | 59,150 | 63,398 | 58,971 |

MLDSA zstd-22 savings are **2.1% / 3.7%**. MLDSA-44 raw size increases 0.9%;
MLDSA-65 raw size decreases 0.4%. Reusing whole interiors can increase raw bytes
when those interiors overlap shorter shared segments; exact reuse is not a
guarantee of minimum raw or compressed size.

The actual mdoc LFA2 archive, streaming zstd, excluding the benchmark container's
32-byte trusted-ID prefix:

| Policy | Raw | z16 | z22 |
|---|---:|---:|---:|
| Current | 770,782 | 183,465 | 162,101 |
| Whole-template numbering, standard segmentation | 759,881 | 179,613 | 157,868 |
| Whole-template numbering, boundary32 | 1,020,291 | 199,144 | 178,098 |
| Whole-template numbering, exact-interior reuse | 787,281 | 177,491 | 156,579 |

The common candidate saves **3.4% compressed** on this mdoc archive but increases
its raw size 2.1%. Compressed standalone sizes are not additive.

## Controls: numbering versus traversal versus segmentation

These rows all use shape-first template traversal; only numbering and segmentation
vary. Values are zstd-22 bytes. This factorial comparison avoids attributing all
of the gain to numbering alone.

| Numbering / segmentation | MLDSA-44 | MLDSA-65 | mdoc hash2 | mdoc signature |
|---|---:|---:|---:|---:|
| No renaming / standard | 1,023,325 | 1,052,393 | 102,131 | 64,284 |
| No renaming / exact-interior reuse | 973,787 | 992,205 | 102,131 | 64,187 |
| Whole-template / standard | 989,455 | 1,011,951 | 99,594 | 59,836 |
| Whole-template / boundary32 | 948,952 | 967,792 | 115,315 | 64,519 |
| Whole-template / exact-interior reuse | 939,456 | 953,232 | 99,594 | 58,971 |
| Per-layer template / standard | 990,865 | 1,012,292 | 99,763 | 59,818 |
| Per-layer template / boundary32 | 948,663 | 967,946 | 115,513 | 64,516 |

The no-renaming standard controls come from the preceding
[template-order experiment](TEMPLATE_ORDER_LFC2_REPORT.md). The new no-renaming
reuse controls were measured here. Per-layer numbering groups exact layer
programs but does not enforce whole-DAG family placement; it provides no clear
advantage. The whole-family policy has the stronger causal guarantee.

Also tested: keep the current global absolute shape/output-major traversal after
renumbering, rather than template traversal. With whole-template numbering and
standard segmentation this gives MLDSA-44/65 982,890 / 1,028,242 bytes and mdoc
hash/signature 99,328 / 59,977. Thus numbering alone does not beat current on MLDSA.

All 40 new candidate results, including LFC1 sizes and raw dictionary/segment/token
counts, are in [results/template-wire-sizes.csv](results/template-wire-sizes.csv).
Size-sweep build/decode times are diagnostic only, not isolated timing benchmarks.

## Did the proposed map-to-translation transformation actually happen?

Yes, for the discovered corresponding blocks. The following compares **the same
original template programs and local traversal** before/after numbering, rather
than re-discovering different matches and calling them an improvement.

| Circuit | Interior terms examined | Distinct interior sequences before | After |
|---|---:|---:|---:|
| MLDSA-44 | 5,454,797 | 4,491 | 4,178 |
| MLDSA-65 | 6,636,722 | 5,795 | 5,412 |
| mdoc hash2 | 1,361 | 56 | 35 |
| mdoc signature | 96,834 | 91 | 60 |

These are whole shape-interior sequences of at least two terms, omitting only
their initial boundary delta. Counts are grouped by exact local template;
different templates are not deduplicated against each other for this diagnostic.

For MLDSA-44, all 279,757 compared output maps and internal-input maps are uniform
translations after numbering; originally 277,327 / 276,303 were. MLDSA-65 similarly
goes from 325,973 / 324,438 to 329,729 / 329,729. These counts include each group's
reference instance, singleton-width maps and empty internal-input maps. They are
not counts of nontrivial independent SHAKE components. Original inputs and shared
constant ports are deliberately excluded from the internal-input translation test.

However, the final LFC2 delta repertoire shrinks only modestly:

| Circuit | Current distinct deltas | Candidate |
|---|---:|---:|
| MLDSA-44 | 178,492 | 177,498 |
| MLDSA-65 | 176,295 | 174,758 |
| mdoc hash2 | 18,210 | 18,078 |
| mdoc signature | 12,708 | 11,722 |

The counts are sums of per-layer dictionaries. The proposal does turn more local
maps into translations, but most matched maps were already translations. Fixed
inputs and shared ports do not become translated private wires, and unmatched
programs do not become copies. This explains why the measured gain is much
smaller than LTP's former local-program/mapping encoding savings. It is not a
proof that no further renumbering or segmentation improvement exists.

Correspondence and layout counters:
[results/template-wire-correspondence.csv](results/template-wire-correspondence.csv).

This uses the existing decomposition's local labels and exact matching. It is
not a general graph-isomorphism search over every possible local permutation.

### Where the remaining representation is large

The saved candidate's delta dictionary is **not dominated by one layer**.
MLDSA-44's largest layer dictionary is 9,894 of 177,498 deltas; MLDSA-65's is
11,413 of 174,758. Numbering has not eliminated a single giant delta outlier.

The layer directly consuming fixed original inputs remains especially expensive
in segment references: it contains 393,080 / 449,700 segment-dictionary entries
(38.7% / 41.1% of the totals) and 61,252 / 97,690 tokens (64.8% / 72.1%) for
MLDSA-44/65. Its term counts remain 2,267,869 / 3,482,504. This is a useful next
target for sequence analysis, but these are integer counts, not independently
attributable zstd byte sizes, and do not identify an FFT or SHAKE source region.

Across all layers the candidate reduces tokens from 209,562 to 94,466 (44) and
252,539 to 135,474 (65), while increasing segment-dictionary entries from
907,282 to 1,015,371 and 996,392 to 1,093,707. Longer exact templates share fewer
short subsegments with other templates. That trade-off helps explain why token
reduction does not translate into a comparable compressed-size reduction.

Full before/after layer counts:
[results/template-wire-layers.csv](results/template-wire-layers.csv).

## Proof performance and implications

Five sequential repetitions per circuit/profile, the same default-allocator
release binary, with no overlapping builds or size/compression jobs. Medians:

| Circuit | Policy | Prover ms | Verifier ms | Load + ID ms | Proof bytes |
|---|---|---:|---:|---:|---:|
| mldsa44 | Current | 1075.0 | 651.5 | 177.8 | 665416 |
| mldsa44 | Numbered, standard segments | 1083.3 | 654.2 | 178.9 | 665192 |
| mldsa44 | Numbered, reused interiors | 1077.0 | 654.9 | 176.6 | 665192 |
| mldsa65 | Current | 1207.5 | 729.9 | 214.4 | 719368 |
| mldsa65 | Numbered, standard segments | 1215.2 | 739.8 | 215.0 | 719176 |
| mldsa65 | Numbered, reused interiors | 1215.6 | 735.0 | 212.9 | 719176 |
| mdoc | Current | 352.0 | 184.1 | included | 344236 |
| mdoc | Numbered, standard segments | 350.0 | 183.7 | included | 343148 |
| mdoc | Numbered, reused interiors | 348.0 | 184.4 | included | 343148 |

MLDSA prover = commit + prove; circuit load/ID, input preparation, and proof
serialization/deserialization are outside the reported core timers. Load includes
one ID check, with an additional untimed check before proving. The mdoc timer is
the full application flow, including decompression, decode and proof serialization;
its trusted loader does not recompute circuit IDs. These scopes are not directly
comparable across applications. All measurements use the same existing unit-
coefficient arithmetic optimization; no runtime arithmetic changed in this turn.

There is no material speed improvement demonstrated. mdoc remains below the
380 ms target on this two-attribute fixture. Use this paired comparison, not the
337 ms baseline from the preceding run, to avoid attributing run-to-run variation
to wire numbering.

Renumbering changes the existing order-sensitive circuit ID and transcript
challenges; that algorithm itself is untouched. Proof geometry is unchanged:
MLDSA-44 has 125,766 witnesses, 37 constraints and block_enc 5,699; MLDSA-65 has
149,677, 37 and 6,113 (rateinv 4, nreq 128). The small proof-byte changes are from
transcript-dependent Merkle multiproof sharing, not added/removed witnesses.
There is no guarantee that every random transcript gives a smaller byte count.

Every timed proof was serialized, decoded and verified. Standard and reused-
interior segmentation of the numbered circuit additionally produced byte-identical
deterministic proofs, confirming that the segmentation change is representation-
only. All terms, widths and depths remain those in the preceding report's geometry
table. Raw samples: [results/template-wire-timings.csv](results/template-wire-timings.csv).

## Actual memory utilization

Separate allocation-tracking build, one proof/verification per fresh process,
`/usr/bin/time -v` for process peak RSS. No circuit compilation, archive preparation
or compression in measured processes. The timing build does not track allocations.

| Circuit | Policy | Peak RSS MiB | Prover live-heap peak MiB | Verifier live-heap peak MiB |
|---|---|---:|---:|---:|
| mdoc | Current | 102.66 | 92.48 | 38.07 |
| mdoc | Numbered, standard segments | 102.29 | 92.45 | 38.03 |
| mdoc | Numbered, reused interiors | 102.95 | 92.55 | 38.13 |
| mldsa44 | Current | 121.22 | 117.99 | 33.41 |
| mldsa44 | Numbered, standard segments | 121.96 | 118.67 | 34.09 |
| mldsa44 | Numbered, reused interiors | 121.74 | 117.72 | 33.14 |
| mldsa65 | Current | 131.04 | 129.49 | 40.12 |
| mldsa65 | Numbered, standard segments | 132.08 | 130.40 | 41.02 |
| mldsa65 | Numbered, reused interiors | 130.93 | 129.15 | 39.78 |

RSS is a whole-process high-water mark, not verifier-only memory. Tracked heap is
the live allocation total at each phase's peak, excluding stacks/code and freed
memory retained by the allocator. The MLDSA verifier phase retains the benchmark's
prepared input vector. Phase-added scratch is unchanged by numbering: MLDSA-44/65
prover 86.10/90.42 MiB, verifier 21.03/24.14 MiB. Total live heap differs because
the resident LFC2 dictionaries/segments differ. The candidate reduces MLDSA live
heap slightly; mdoc memory is effectively unchanged.

Exact byte counts: [results/template-wire-memory.csv](results/template-wire-memory.csv).

## Reproduction

```sh
cargo test --release -p circuits-experimental --test layer_templates --no-run
ORDER_DATASET=mldsa44 ORDER_WIRE_POLICY=whole ORDER_COMPONENTS=3 \
ORDER_TRAVERSALS=shape_instances ORDER_SEGMENTS=standard,boundary32,reuse \
ORDER_SAVE_DIR=target/template-wire-lfc2 \
  cargo test --release -p circuits-experimental --test layer_templates \
  layer_template_order_sweep -- --ignored --nocapture
```

Use `ORDER_WIRE_POLICY=layer` for per-layer-family placement, `none` for no
renaming, and `ORDER_COMPONENTS=5` for the current global shape/output-major
traversal after renaming. Component 3 chooses shape-first template traversal.
Inputs default to `target/traversal-circuits/DATASET--kind_abs_lex0213_r5.lfc2`.
`ORDER_INPUT_CIRCUIT` overrides the path. `ORDER_LAYER_STATS=1` prints per-layer
counts from a saved LFC2 file without running a sweep.

Proof benchmark commands and measurement boundaries are shared with
[TEMPLATE_ORDER_LFC2_REPORT.md](TEMPLATE_ORDER_LFC2_REPORT.md). Candidate files
are named `DATASET-wire_whole-b3-w10000000-o4-shape_instances-reuse.lfc2`.

## Validation completed

- All 40 size candidates pass exact term/traversal and LFC2 serialization/ID
  round trips. Every renumbered source has an explicit checked inverse bijection;
  input/output maps are asserted to be identity and geometry is retained.
- 45 timed and 9 fresh-memory proof/verification flows pass on MLDSA-44,
  MLDSA-65 and current two-attribute mdoc. This does not claim a benchmark sweep
  of all four mdoc attribute counts or a proof run of every experimental selector.
- `cargo test --release -p circuits-experimental --test layer_templates --test template_proofs`:
  32 non-ignored tests pass, including translated component maps, fixed boundaries,
  exact inverse preservation of duplicates, malformed-map rejection and exact
  repeated-interior segmentation. Ignored proof tests were run explicitly above.
- `cargo test --release -p core-proto -p runtime-sumcheck -p runtime-zk`: passes.
- `cargo check --workspace --all-targets`: passes without warnings.
- `git diff --check`: passes. No production compiler/prover/reader code was
  changed for this experiment; unrelated dirty worktree changes are preserved.
