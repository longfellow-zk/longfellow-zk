# Alternate flat-LFC2 segmentation: pair, phrase, and dictionary experiments

## Outcome

Tested **104 distinct policies** on MLDSA44, MLDSA65, mdoc signature, and mdoc hash2:
416 distinct circuit variants, **444 successful size/identity checks** including repeated
controls, and 111 actual combined mdoc archive measurements. The benchmark is complete
serialized bytes after **zstd level 22**. Raw bytes and level 16 are also recorded.

The main findings are:

- Pair parsing is very effective at reducing **uncompressed** LFC2, but is not the
  best compressed-size policy for MLDSA. Pruned delta Re-Pair gives raw sizes of
  **942,255 / 997,577 bytes**, but zstd sizes of **371,594 / 375,943 bytes**.
- The largest new MLDSA compressed improvement comes from **dictionary locality**,
  not additional pair merges. CDC residual segmentation plus shared template interiors,
  followed by suffix ordering of the segment dictionary, gives **351,542 / 358,360 bytes**.
- Prefix factoring adds a smaller further improvement. The measured individual minima
  are **349,727 bytes for MLDSA44** and **356,269 bytes for MLDSA65**, at different
  prefix thresholds. These are **not one common policy**.
- Best combined mdoc is **145,818 bytes** (raw **1,050,401**) using CDC-seeded,
  pruned Re-Pair. That is only 522 bytes below the previous best CDC/reuse archive.
  This policy is worse for MLDSA, so it is not a universal replacement.
- No production policy was changed. All results remain **ordinary flat LFC2**, directly
  consumable by the existing hand-major prover. No recursive runtime grammar, new
  circuit format, runtime sorting, or runtime hash table was introduced.

The individual compressed minima improve on the previous measured minima by 3.64%
(MLDSA44), 3.30% (MLDSA65), and 0.36% (mdoc archive). This comparison does not imply
that one policy achieves all three minima.

## Raw and compressed sizes

Every cell below is **raw bytes / zstd-22 bytes**. mdoc is the actual jointly encoded
LFA2 archive, not the sum of two separately compressed circuits. All dictionary,
reference, coefficient, header, and circuit-ID overhead is included.
Standalone LFC2 uses bulk zstd compression; the combined archive uses the same
streaming zstd path as the existing archive benchmark. The saved `.archive` test
container prepends a separate 32-byte trusted-spec ID to its level-16 frame; that
test-only wrapper is not part of LFA2 or the archive sizes in the tables. Add 32
bytes to the reported level-16 archive size for that container's on-disk size.

| Common policy applied to all circuits | MLDSA44 | MLDSA65 | mdoc archive |
|---|---:|---:|---:|
| Selected template/reuse baseline | 1,642,397 / 367,947 | 1,805,553 / 377,432 | 789,028 / 156,667 |
| Previous CDC-128 + reuse | 2,030,895 / 363,275 | 2,205,120 / 369,259 | 1,009,975 / 146,340 |
| Delta Re-Pair-512, pruned | 942,255 / 371,594 | 997,577 / 375,943 | 421,936 / 159,472 |
| CDC-seeded Re-Pair-8192, pruned | 2,207,291 / 382,501 | 2,329,327 / 386,096 | 1,050,401 / 145,818 |
| CDC/reuse + suffix dictionary order | 2,032,118 / 351,542 | 2,206,603 / 358,360 | 1,022,504 / 150,983 |
| CDC/reuse + prefix-32 factoring + bucketed suffix order | 1,856,648 / 349,727 | 2,021,330 / 359,537 | 923,922 / 152,005 |
| CDC/reuse + prefix-128 factoring + bucketed suffix order | 1,874,970 / 352,705 | 2,041,745 / 356,269 | 937,816 / 151,807 |
| CDC/reuse + prefix/suffix-8 factoring + bucketed suffix order | 1,653,777 / 350,637 | 1,832,319 / 358,333 | 801,489 / 153,060 |

The last policy keeps raw storage close to the selected baseline while improving
compressed size for all three workloads relative to that baseline. It does **not**
preserve the previous best mdoc archive size: 153,060 versus 146,340 bytes.
Suffix dictionary ordering alone also increases mdoc relative to that previous
CDC best, despite improving it relative to the selected 156,667-byte baseline.

### Individual circuit minima

| Circuit | Policy | Raw bytes | zstd-16 | zstd-22 |
|---|---|---:|---:|---:|
| MLDSA44 | Prefix-32 factoring + bucketed suffix order on CDC/reuse | 1,856,648 | 385,883 | 349,727 |
| MLDSA65 | Prefix-128 factoring + bucketed suffix order on CDC/reuse | 2,041,745 | 393,294 | 356,269 |
| mdoc signature | Prefix/suffix-32 factoring on CDC/reuse | 227,756 | 54,888 | 54,514 |
| mdoc hash2 | Stock-64-seeded ranked batch pairs, cap 8192 | 1,211,986 | 103,001 | 91,383 |
| Combined mdoc archive | CDC-seeded Re-Pair-8192, pruned | 1,050,401 | 167,694 | 145,818 |

The standalone mdoc minima do not define the archive minimum. Compression across
the two circuits and the archive's shared data must be measured jointly.
Raw serialized bytes are not an estimate of resident memory.

## What was tested

All tests hold the existing `whole / shape_classes` wire numbering and term traversal
fixed. MLDSA uses period 4, a special first round, no bit pluckers, the XOR-basis SHAKE
witnesses, an `ninput` subfield boundary, and 3/18-byte field serialization. These are
the selected saved fixtures; no source-circuit parameter was varied in this experiment.

### Binary pair variants

The alphabet is the layer's existing delta IDs, including the coefficient index.
No delta tuple is approximated or replaced. Pair algorithms were applied either to
individual delta symbols, stock-64 segment references, or CDC-128 segment references.

- **Exact frequency Re-Pair:** repeatedly choose the pair with the greatest current
  adjacency count, breaking ties by pair IDs. Replace its nonoverlapping occurrences
  left to right. Counts include overlapping adjacencies; rules with fewer than two
  actual replacements are rejected. A linked sequence, occurrence sets, and a lazy
  priority queue implement this offline search. A slow recounting reference test
  checks the implementation, including self-pair overlaps.
- **Left-greedy batch pairs:** merge eligible pairs left to right, refreshing counts
  between passes.
- **Ranked batch pairs:** prefer the higher-scoring of adjacent conflicting pairs.
  This is a local-priority approximation, explicitly not exact Re-Pair.
- **Aligned batch pairs:** consider only even/odd pairs on each pass. This tests
  phase-sensitive binary grouping; it was substantially worse.
- **Flat-gain variants:** rank/filter merges using two estimated saved bytes per
  execution token, minus the complete flattened phrase body and length prefix.
  Parent-body deletion is not credited. This is a conservative raw-storage proxy,
  not an exact raw-size or zstd objective.
- **Grammar pruning:** after learning pairs, choose a cut through the grammar using
  amortized flat-body costs. Descendant usage counts can overestimate actual selected
  uses if an ancestor is retained, so this is a heuristic, not a global optimum.

New pair-phrase length caps included 32, 128, 512, 2048, 8192, and 65536 where relevant.
Existing seed phrases are not truncated if longer than a cap. Most variants coalesce
singleton and one-use final phrases into literal runs of at most 64 deltas; explicit
`raw` variants disable this. The cap controls pair construction, not that final
literal grouping or the separately retained template interiors.

**There is no hidden recursive-format saving.** Intermediate rules are discarded.
Every final phrase is expanded to delta IDs, identical complete phrases are interned,
and the actual flat segment dictionary and execution tokens are serialized as LFC2.
The grammar expansion itself is checked before discarding it.

### Other segmentation and packing controls

- **LZ78:** prefix-dictionary phrase discovery, capped at 32/128/512 deltas, then
  flattened into LFC2. This performed very poorly: at cap 128, MLDSA44 was
  12,561,352 bytes raw and 2,745,408 bytes compressed. LZ78 normally benefits from
  recursive prefix references; their full flattening is expensive here.
- **Template-interior preservation:** run the alternative segmenter as a base, then
  retain exact repeated template interiors as single segments, splitting the base
  parse only at their boundaries. This is the existing `reuse_` mechanism, not a
  workload-dependent size chooser.
- **Prefix/suffix factoring:** build an implicit radix trie over the distinct stored
  segment bodies. Split at shared branch prefixes after at least 8/32/128 deltas;
  repeat on reversed bodies for suffix extraction. Re-intern all resulting flat
  fragments and charge all additional execution references. This shares smaller
  pieces across nonidentical dictionary entries without changing any term order.
- **Dictionary order:** order whole segment bodies lexicographically, by suffix,
  or by length then lexicographically. Bucketed variants first preserve each segment
  reference's ULEB width class and cluster within it. Those variants leave raw byte
  counts unchanged. Suffix sorting compares bodies backward but does **not** reverse
  their stored or executed delta order. Delta dictionaries remain unchanged.

The main suite had 38 policies, refinement 42, and factoring 31. Repeated controls
were byte-identical across suites. The union contains 104 policies.

## Why fewer dictionary entries do not imply better zstd size

For MLDSA44, the following are measured **raw section sizes**. Header/constants/ID
are outside these sections.

| Policy | Delta table bytes | Segment dictionary bytes | Execution-token bytes | Whole-circuit zstd-22 |
|---|---:|---:|---:|---:|
| CDC/reuse | 258,357 | 1,729,908 | 22,467 | 363,275 |
| Same parse, bucketed suffix order | 258,357 | 1,729,908 | 22,467 | 351,999 |
| Delta Re-Pair-128 | 258,357 | 825,151 | 98,296 | 377,214 |
| Delta flat-gain pairs, cap 32 | 258,357 | 432,771 | 663,590 | 411,552 |

Two causal controls are particularly useful:

1. **Ordering alone:** bucketed suffix ordering preserves the exact phrase set,
   references, their widths, and every raw section size, yet saves 11,276 compressed
   bytes on MLDSA44. Independent per-layer segment-section compression drops in
   aggregate from 246,712 to 227,910 bytes; token-section compression barely changes
   (7,603 to 7,588). This supports dictionary-body locality as the source of the gain.
   Those independent section-frame sizes are diagnostic and are **not additive**
   contributions to the whole-circuit compressed size.
2. **Flat-gain objective mismatch:** delta flat-gain parsing reduces the stored body
   entries from 1,181,739 to 227,201, but increases execution references from 15,629
   to 406,830. Its token sections compress independently to 77,734 bytes rather than
   7,603. The full circuit gets larger after zstd despite a much smaller raw dictionary.

The mdoc control goes the other direction: bucketed suffix ordering on the same CDC
hash2 parse increases the independently compressed segment sections from 56,905 to
59,428 bytes. Thus dictionary clustering is not an automatic universal win; its
interaction with the existing body layout is measurable, not just speculative.

Larger pair caps can also inflate flat dictionaries with little compressed benefit.
For example, stock-seeded Re-Pair-8192 without preserved interiors produces MLDSA65
raw size 5,950,044 bytes, yet still compresses to 403,368—worse than the existing
1,805,553 / 377,432-byte template/reuse baseline.

Distinct delta counts never change in this experiment: MLDSA44 **49,849**, MLDSA65
**51,169**, mdoc signature **11,697**, and mdoc hash2 **18,051** (sums of per-layer
dictionary counts). The gains are entirely in segmentation and dictionary layout.

## Correctness and proof implications

- Release/native build (`target-cpu=native`), **48 unit tests passed**, 2 offline tests
  ignored in the normal unit run. Pair tests include empty, short, overlapping,
  periodic, shifted, randomized, seeded, pruned, and deterministic cases.
- Every one of the 444 circuit cases passed expanded-delta equality, geometry and
  input-boundary checks, circuit-ID recomputation, decoder validation, and
  byte-identical LFC2 read/write round-trip.
- **18 end-to-end prover/verifier flows** passed across six representative policies
  and all three workloads, including both MLDSA compressed-minimum policies, the
  mdoc archive minimum, the raw-minimum pair policy, suffix ordering, and the
  low-raw-overhead prefix/suffix policy.
- These flows required **byte-for-byte equality with the saved baseline proofs**:
  MLDSA44 **218,708 bytes**, MLDSA65 **227,852**, mdoc **343,436**.
- No wires, terms, layers, inputs, witnesses, circuit IDs, or proofs were changed.
  Geometry remains MLDSA44 3,613,574 wires / 6,691,580 terms / 24 layers;
  MLDSA65 3,791,554 / 8,064,583 / 24;
  mdoc signature 183,618 / 276,481 / 21;
  mdoc hash2 3,473,933 / 6,394,835 / 20.
- These were correctness/size experiments, not controlled prover-time or peak-memory
  benchmarks. Offline segmentation timings are in the CSVs but were collected with
  concurrent jobs. No runtime speed conclusion should be drawn from them.
- All new work is in experimental code/support files. C++ remains at HEAD.

## Recommendation

Do not replace the current policy with generic binary-pair parsing solely because
its flat dictionary is smaller. It optimizes a different objective from zstd size.

For a simple compressed-size experiment, **retain template interiors, use CDC-128
for the base/residual parse, and suffix-cluster segment bodies**. It gives a clear
MLDSA improvement and stays below the selected mdoc baseline, with no runtime format
change. However, explicitly accept its mdoc regression against the *best prior CDC*
result before adopting it. Prefix/suffix factoring offers a further raw-size trade-off;
it is not necessary to demonstrate the principal compression gain.

There is no measured common policy that attains every workload's individual minimum.
The report does not install per-circuit selection, “try both and pick,” or a majority
threshold. The production default is left untouched for a separate adoption decision.

## Artifacts and reproduction

- [Compact raw/zstd tables](results/pair-segmentation-tables.md)
- [All 416 distinct circuit rows, including raw and zstd-16/22](results/pair-segmentation-circuits.csv)
- [All 104 common policies with actual mdoc archive sizes](results/pair-segmentation-shared.csv)
- [Per-layer raw sections and independent compression diagnostics](results/pair-segmentation-sections.csv)
- `pair_segments.rs`, `segment_extract.rs`, `segment_dictionary.rs`: offline algorithms.
- `run_pair_sweep.py`: fixed `main`, `refine`, and `factor` suites.
- `validate_pair_sweep.py`: the 18 baseline-proof equality flows.
- `publish_pair_sweep.py`: merged tables and section diagnostics.

Build the `scheduling_sweep` release test with feature `mldsa-slicing-experiment`, then
run `run_pair_sweep.py screen --suite main|refine|factor --root <fresh-output-root>`.
Each run stores its exact executable, SHA-256, manifest, logs, and LFC2 outputs.
Use `run_pair_sweep.py summary --root ...`, then `summarize_scheduling_sweep.py archives`
and `summary --root ...` to produce actual archive measurements. A changed executable
requires a fresh root; do not overwrite the recorded experiments.

Recorded roots are `target/pair-segmentation-v1`, `target/pair-segmentation-refine`,
and `target/pair-segmentation-factor`. Validation logs are in
`target/pair-segmentation-validation`; the final unit log is
`target/pair-segmentation-v1/unit-tests-final.log`.
