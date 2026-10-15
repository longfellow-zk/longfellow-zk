# Fixed-geometry traversal and connected-component experiments

2026-09-11, `rust` working tree based on `fa578cc5`; integrated MLDSA sources
from `mldsa` commit `e8794c5`. These experiments do not change the production
scheduler, prover, verifier, format, or registered circuit IDs.

## Conclusion

The existing shape-first/output-major policy remains the best balanced policy
in this search. There is no substantial improvement shared by MLDSA-44,
MLDSA-65, mdoc hash, and mdoc signature. In particular, none of these ordering
experiments reaches 500,000 compressed bytes for either MLDSA circuit.

There are individual wins, but they conflict. A shape/arity/input-major policy
helps mdoc hash; components detected within shapes help mdoc signature; those
same policies enlarge MLDSA. This is evidence against replacing the shared
policy with a circuit-size majority threshold or a runtime/compiler tournament.

## Scope and method

The main sweep covers MLDSA-44, MLDSA-65, the current two-attribute mdoc hash
circuit, and the mdoc signature circuit. Additional final-candidate checks cover
mdoc hash circuits for one through four attributes.

- **505 named traversal policies per main circuit**, including the numeric-minimum
  component-order follow-up: 2,020 policy/dataset combinations. Identical streams
  within a sweep are detected by ID and recorded as aliases. There were
  453 / 453 / 463 / 454 full size measurements respectively, excluding
  final-candidate reruns.
- Another 42 delta/segment dictionary orderings per circuit hold even the term
  stream and circuit ID fixed.
- All wire IDs, primary input order, terms including coefficients and assertion
  markers, layer widths/depth, and witness geometry are fixed. No unroll changes,
  extra witnesses, operand swaps, or wire renumbering are used.
- Period 6, XOR-basis SHAKE, the Fp24 degree-six extension, and CRT interpolation
  are unchanged in MLDSA.
- Sizes are complete ordinary LFC2 files, including constants, metadata, every
  dictionary, all segment tokens, and the circuit ID. There is no omitted mapping
  or template overhead. Segmentation is the existing 32-term implementation.
- Individual circuit comparisons use `zstd::bulk::compress(..., 16)`. Level 3 is
  also recorded for every traversal. Final candidates additionally measure LFC1,
  unsegmented LFC2, and level 22. Archive checks use the production streaming
  compressor; bulk and streaming results must not be conflated.
- Size jobs run concurrently on the same Ryzen 9 9950X machine. Their elapsed
  times, and the proof-validation timings while these jobs run, are **not** a
  controlled prover/verifier performance comparison.

The harness sorts an index permutation, preserving every term by construction.
Finalists additionally undergo exact semantic term-multiset comparison and
ID-checked LFC2 round trips. Semantic comparison resolves coefficient bytes:
the existing segmenter legitimately reindexes the coefficient dictionary.

## Traversal families

Coordinates in policy names are `0=g`, `1=h0`, `2=h1`, `3=coefficient-byte rank`.
`lex0213_r5` means descending g, descending h1, ascending h0, then ascending
coefficient bytes. Mask bits select which coordinate directions are reversed.

The sweep includes:

- All six coordinate priorities and all eight coordinate direction combinations,
  globally and after shape separation.
- Two- and three-dimensional Morton traversals, Hilbert traversals, operand-gap
  keys, and input-minus-output relative-coordinate keys.
- Constant/linear/square/product shape grouping; explicit constant operand side;
  zero/one/minus-one/general coefficient classes; full coefficient grouping;
  and assertion-marker separation.
- Transposing the ordinal term position within an output/shape, grouping by
  per-output shape arity, and exact translated gate-shape signatures with and
  without coefficients. Signature equality uses full vectors, not wire counts
  or an unchecked hash.
- Hybrid rules that preserve multi-term shape bodies in output-major order and
  apply different priorities/coefficient grouping only to single-term shapes.

Here, a linear term has exactly one operand known to equal One; a square has
equal non-One operands. Constant propagation recognizes copies of One at any
wire ID, not just numeric wire zero. No witness values influence a policy.

### Connected-component follow-up

Global components use the complete layered graph, with primary inputs treated
as external ports. Variants exclude all proven constants or only proven One,
and either retain or ignore zero-coefficient assertion-marker edges.

Layer-local variants use a bipartite input/output graph. The `bip0` variants
exclude One and its copies, and exclude primary-input sharing at the first
layer. `bip1` is an explicit full-edge control, including constant/primary-input
sharing; it is not a proposal to reinterpret those inputs as internal wires.

Both component-before-shape and shape-before-component orders are tested, as
well as components detected independently inside each term shape. Within groups,
absolute, offset-normalized, and rank-normalized Morton coordinates are tested
alongside lexicographic orders. These change traversal only: normalized values
are sorting keys, never replacement wire IDs in the circuit.

The initial per-layer component ordering takes the minimum input-first vertex
ID. A final follow-up compares the minimum numeric wire ID across both sides,
with side used only to break equal-number ties. Input and output vertices remain
distinct graph vertices in every case.

## Representative results

Complete segmented LFC2 + zstd-16, **bytes**. Every row is one fixed policy applied
to all four circuits; these are not per-circuit selections.

| Fixed policy | MLDSA-44 | MLDSA-65 | mdoc hash, 2 attrs | mdoc signature |
|---|---:|---:|---:|---:|
| Global Morton control | 3,857,534 | 3,877,321 | 191,624 | 130,134 |
| Global input lexicographic, h0/h1/g | 1,303,219 | 1,326,494 | 569,832 | 108,764 |
| **Current: shape, g descending, h1 descending, h0 ascending** | **997,383** | **1,031,363** | **112,990** | **63,443** |
| Same, but h1 ascending | 995,011 | 1,026,343 | 112,717 | 63,905 |
| Shape, term ordinal, output-major | 1,082,623 | 1,105,561 | 165,528 | 68,484 |
| Shape, full coefficient, output-major | 1,943,980 | 2,328,439 | 175,129 | 63,439 |
| Shape, coefficient class, output-major | 1,171,816 | 1,205,594 | 113,842 | 54,430 |
| Shape, arity, h1/g/h0 ascending | 1,045,170 | 1,075,974 | 95,139 | 63,839 |
| Shape, exact translated gate signature, output-major | 2,572,867 | 2,617,780 | 293,723 | 132,913 |
| Shape, singleton/multi-term hybrid | 1,008,436 | 1,021,912 | 114,609 | 65,222 |
| Shape, global component, output-major | 1,015,294 | 1,037,997 | 113,722 | 64,736 |
| Shape, bipartite component excluding One, output-major | 1,384,291 | 1,405,211 | 195,304 | 65,081 |
| Shape, full-edge bipartite component, output-major | 1,050,260 | 1,081,993 | 111,103 | 55,545 |
| Bipartite components within each shape, excluding One | 1,156,787 | 1,180,386 | 169,865 | 57,649 |
| Bipartite components within each shape, full-edge control | 1,141,757 | 1,153,044 | 166,839 | 53,227 |

Changing global connectivity to exclude only One produced exactly the same
shape-first/output-major sizes as excluding all proven constants. Dropping
zero-coefficient edges gave 1,014,736 / 1,037,370 / 113,915 / 64,628 bytes: no
shared improvement.

The individual traversal minima were
994,992 / 1,021,912 / 95,139 / 53,227 bytes. These use **different policies** and are
only diagnostic lower envelopes of this search, not a proposed selection rule.
The MLDSA minima improve on the current shared policy by only 0.24% and 0.92%.

Using the minimum numeric wire ID across both sides to order layer components
does not change that conclusion. For shape-first bipartite components excluding
One, it gives 1,699,402 / 1,669,525 / 186,466 / 73,299 bytes. The full-edge version
gives 1,149,928 / 1,151,618 / 111,469 / 58,219 bytes. No numeric-minimum candidate
improves on the existing four individual minima or gives a shared winner.

## What the measurements explain

### Separating term shapes matters much more than reversing an axis

Holding the output-major coordinate priority/directions fixed, adding the four
shape groups reduces MLDSA-44 from 9,543,361 to 997,383 bytes. This is a controlled
comparison: only the grouping changes. Constant coordinates, square diagonals,
and general products otherwise alternate in the delta stream. Shape separation
keeps their different coordinate patterns from repeatedly interrupting one
another; output-major traversal then retains the local multi-term gate bodies.

This does not prove that absolute Morton's translation sensitivity explains the
entire old gap. Lexicographic traversal is translation invariant, but changing
shape grouping, coordinate priority, component ordering, and traversal are
distinct interventions. Local Morton did not produce a shared winner here.

### Connectedness is not the same thing as encoding similarity

On MLDSA-44, the current policy has 178,492 layer-local delta entries and 30,026
segments. Shape-first global components give 179,679 and 30,144: slightly worse.
Shape-first bipartite components excluding One give 267,175 and 29,672: fewer
segments, but many more distinct deltas and a substantially larger file.

Component boundaries describe dependencies, not necessarily equal affine wire
offsets or equal sequences of term shapes. Keeping a whole component together
can separate patterns that would otherwise compress together. Grouping exact
translated gate signatures also performs poorly here; verified local shape
equality alone does not guarantee a better complete-file term sequence.

### Neither distinct-delta count nor raw size is the objective

For mdoc signature, shape-first bipartite grouping excluding One reduces delta
entries from 12,708 to 10,556 and raw LFC2 from 222,143 to 190,352 bytes, but
**increases** zstd size from 63,443 to 65,081 bytes.

For MLDSA-44, shape/arity/h1-major ordering reduces raw LFC2 to 2,590,353 bytes,
below the current 2,670,639, but raises compressed size to 1,045,170 bytes.
Both dictionary cost and repetition in the encoded segment/token sequence matter.

### Dictionary ordering is a separate, compatibility-preserving lever

The extra sweep reorders delta dictionaries and remaps their references, and
optionally reorders segment dictionaries and remaps their tokens. It tests all
six delta-coordinate priorities in unsigned and zigzag-value order, global delta
frequency, and three segment ordering rules. It never changes the delta stream,
distinct-delta counts, circuit ID, or proof transcript.

Sorting delta dictionaries by zigzag(g), zigzag(h1), zigzag(h0), coefficient,
while retaining frequency-ordered segments, gives:

| Circuit | Current raw → alternative raw | Current zstd-16 → alternative |
|---|---:|---:|
| MLDSA-44 | 2,670,639 → 2,892,826 | 997,383 → 975,655 |
| MLDSA-65 | 2,896,804 → 3,148,110 | 1,031,363 → 992,176 |
| mdoc hash | 548,467 → 612,766 | 112,990 → 113,428 |
| mdoc signature | 222,143 → 275,804 | 63,443 → 75,357 |

Thus even the best MLDSA dictionary rule is not a shared improvement. It saves
2.18% / 3.80% for MLDSA, but hurts mdoc and increases serialized raw size. All 168
dictionary experiments passed ID-checked decoding and exact expanded-delta-stream
comparison. This is not an invertible tuple transform purported to reduce the
number of distinct deltas: it changes dictionary order and integer reference IDs.

## Remaining representation cost

Current policy, complete individual files, bulk compression:

| Circuit | LFC1 | LFC1 zstd-16 | Segmented LFC2 | LFC2 zstd-16 | LFC2 zstd-22 |
|---|---:|---:|---:|---:|---:|
| MLDSA-44 | 78,996,522 | 669,700 | 2,670,639 | 997,383 | 959,815 |
| MLDSA-65 | 95,475,126 | 861,477 | 2,896,804 | 1,031,363 | 989,616 |
| mdoc hash, 2 attrs | 76,743,313 | 73,677 | 548,467 | 112,990 | 100,969 |
| mdoc signature | 3,337,858 | 47,086 | 222,143 | 63,443 | 63,398 |

Unsegmented LFC2 compresses to 927,292 / 939,962 bytes for MLDSA, but its raw sizes
are 12,273,518 / 14,919,116 bytes. LFC1 and unsegmented LFC2 therefore are not free
replacements for the compact segmented in-memory representation.

The largest independently compressed MLDSA layer body is the first layer:
188,964 / 216,663 bytes. Layers 35 and 36 cost 58,190 / 52,183 bytes for MLDSA-44,
and 67,747 / 62,988 for MLDSA-65; several other layers cost around 39–46 KB.
Independent-layer sizes are diagnostic, not additive contributions to the
whole compressed file. The remaining cost is distributed, not isolated to one
layer that this experiment identifies as a broken FFT.

## Proposed design

1. Retain one deterministic compiler policy: conservative One propagation;
   constant/linear/square/product groups; descending g, descending h1, ascending
   h0; semantic coefficient-byte tie breaking. Keep existing LFC2 segmentation.
2. Keep traversal choice out of the dense prover. It consumes the segmented
   circuit directly; no runtime sorting, mappings, hash table, or template
   expansion is introduced.
3. Do not add graph partitioning, an entropy threshold, or per-circuit search to
   the production policy on the strength of these results. The graph variants
   add complexity without a broad size win, and the hybrid rule did not rescue
   the conflicting single-circuit results.
4. Preserve legacy circuits/IDs and legacy round-major proving separately when
   implementing the previously discussed protocol compatibility switch. Changes
   to term traversal change the statement ID; the dictionary-only experiment
   demonstrates which representation changes can preserve it exactly.
5. For another attempt at 500 KB, investigate **internal wire numbering across
   proven corresponding repeated subcircuits**, with primary inputs fixed, and
   the segmenter's complete-file cost model. Those are proposed next experiments,
   not a claimed solution or a proven lower bound on what term sorting can do.

## mdoc preservation and proof validation

Both the current policy and the h1-ascending near-tie passed complete mdoc proof
generation and verification for 1–4 attributes. The test decodes saved LFC2
files with ID checking, recompiles the reference circuit, checks its exact
semantic term multiset/geometry, builds the ordinary archive, and invokes the
existing application prover/verifier. Three- and four-attribute checks request
subsets of a valid larger presentation, rather than requiring a fixture with
exactly that many attributes.

Complete mdoc archives, production streaming zstd at level 16:

| Attributes | Current raw archive | Current compressed | h1-ascending raw | h1-ascending compressed |
|---|---:|---:|---:|---:|
| 1 | 750,981 | 182,988 | 751,492 | 183,277 |
| 2 | 770,782 | 183,465 | 770,172 | 185,748 |
| 3 | 786,703 | 185,108 | 786,071 | 186,874 |
| 4 | 803,703 | 186,421 | 803,285 | 187,894 |

Thus the small MLDSA savings from changing h1 direction come with an actual mdoc
archive regression, despite almost unchanged sums of individually compressed
circuits. We retain the current policy and its existing experimental IDs.

The h1-ascending MLDSA-44 and MLDSA-65 circuits also pass full proof generation,
serialization, decoding using verifier-derived geometry, and verification.
Their proof sizes in these runs are 665,352 and 719,176 bytes. Witness and fixed
proof geometry are unchanged; term-order changes alter IDs/Fiat–Shamir challenges
and therefore variable-length Merkle multiproofs. These sizes are not a promise
that each proof byte count is invariant under traversal changes.

The ordinary release suite passes 49 tests, with eight explicit offline tests
ignored. Standalone no-default-feature library checking, all-target checking,
format checking, and `git diff --check` pass. The two new validation-harness
assumptions corrected during this work were coefficient-index equality versus
coefficient-value equality, and requiring an exact-count fixture instead of
using a valid attribute subset. Neither required a production change.

## Artifacts and reproduction

- [Complete traversal measurements](results/traversal-summary.csv): one row per
  named policy/dataset, including aliases, all byte sizes and dictionary metrics.
- `results/traversal-{dataset}-{phase}.log`: full configurations, measurements,
  aliases, final LFC1/LFC2 comparisons and layer diagnostics.
- `results/traversal-{dataset}-dictionary.log`: all dictionary-only results.
- `results/traversal-validation-{mdoc,mldsa}.log`: end-to-end validation.
- `results/traversal-unit-tests.log`: ordinary experimental suite.
- `target/traversal-circuits/`: generated finalist LFC2 files, deliberately not
  installed as production circuits.

Build the release test binary with:

```sh
cargo test --release -p circuits-experimental --features testonly --no-run
```

Pass the emitted `experimental_tests` executable to the offline runner:

```sh
python3 experiments/mldsa/run_traversal_sweep.py \
  target/release/deps/experimental_tests-3e71424df7f73b71 \
  core mldsa44 mldsa65 mdoc_hash2 mdoc_sig
```

Repeat with `groups`, `components`, `shapes`, `roles`, `hybrid`,
`component_shapes`, `global_components`, `component_numeric`, and `dictionary`.
The `final` phase measures and saves the current policy and the h1-ascending
near-tie; it also accepts `mdoc_hash1`, `mdoc_hash3`, and `mdoc_hash4`.
No measurement-driven selection is used by the production compiler.
