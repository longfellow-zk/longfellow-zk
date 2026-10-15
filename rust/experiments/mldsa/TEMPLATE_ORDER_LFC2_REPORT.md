# Offline template ordering, ordinary LFC2

Measured 2026-09-12, dirty `rust` worktree based on
`fa578cc5bb055d72df379dc195393ea2f124788e`, Ryzen 9950X, Rust 1.97.1,
release/native. This is a same-runtime comparison against the saved current
circuits, not against clean HEAD or C++.

## Decision

LTP1 is abandoned. Its decoder, layer storage and runtime dispatch were removed;
the old implementation is recoverable at `/tmp/abandoned-ltp-20260912.rs`.
Historical results remain in [LAYER_TEMPLATE_REPORT.md](LAYER_TEMPLATE_REPORT.md).

Template discovery now produces **ordinary LFC2**, including its existing compact
in-memory delta/segment/token representation. It is offline only: no maps,
template decoder, runtime sorting, runtime hash table or new prover protocol.
The dense hand-major prover and both numerical and symbolic verifier consume the
ordinary layer interface. Round-major still requires its existing Morton order;
these experimental traversals are for hand-major only.

The experiment does **not** justify replacing the current shared shape-first
compiler policy. None of the tested template traversals beats it consistently.
Defaults are unchanged; there is no per-circuit candidate chooser.
The strict 500,000-byte compressed MLDSA target remains unmet.

## What was implemented

1. Discover components, project into layers and normalize local wiring for exact
   program matching. Equal wire counts alone are not treated as correspondence.
2. Group identical programs and use their instance maps **offline** to choose an
   absolute term traversal. Preserve every original term, coefficient and input
   hand, including duplicates and assertion markers. No wires are renamed.
3. Difference consecutive absolute `(g,h0,h1)` coordinates continuously, including
   across instance boundaries. Coefficient indices remain absolute, as in LFC2.
4. Use the existing LFC2 segmenter, or experimental exact-run segmentation that
   isolates the first boundary-dependent delta and chunks the rest at 32/128.
5. Write/read ordinary LFC2. Check exact per-layer term multisets, exact traversal
   through segmentation, circuit IDs and byte-exact serialization round trips.

The global discovery control excludes original inputs and **all proven constants**
from connectivity. Per-layer bipartite controls exclude original inputs in both
variants and either exclude or include constant-one wires and their proven copies.
Components are ranked by their minimum wire ID. Grouping may subsequently bring
structurally matching components together. These are offline analysis controls,
not a change to connectivity or arithmetic in the compiled circuit.

Local order is constant/linear/square/product, descending local output,
descending second input, ascending first input, then coefficient bytes.
Four traversal variants were tested: group/instance/term; shape/group/instance/term;
group/term/instance; and shape/group/term/instance. Shape classification uses the
actual mapped wires, including proven copies of one.

## Why flattening did not recover LTP savings

There are two distinct effects:

- **Gate-type transitions:** whole-instance order revisits all four shapes for
  every instance. Changing only the outer traversal to shape-first reduces
  MLDSA-44's distinct deltas from 466,401 to 179,844, close to the existing 178,492.
  For mdoc hash2 the same change gives 69,743 to 18,449, versus 18,210 currently.
  This controlled comparison identifies repeated shape switching as the dominant
  regression of literal flattening; it should not be attributed just to maps.
- **Local reuse is not absolute-delta reuse:** LTP stored a local program once
  plus mappings. LFC2 can reuse a segment only when its actual delta-index sequence
  repeats. An arbitrary input/output mapping need not preserve coordinate
  differences. Translation does preserve interior differences, but not the first
  delta at the join. Boundary-aware segmentation addresses that join without
  inventing maps in the runtime, but does not recover enough repetition here.

Interleaving corresponding terms across instances was also measured and was
worse. These results reject the tested order-only policies, not every possible
ordering or future wire renumbering. No claim of an optimum or impossibility is
being made. FFTs, SHAKE basis, period 6, witnesses and geometry were held fixed.

## Sizes

All sizes are bytes. `z22` means standalone zstd bulk compression at level 22.
All LFC2 headers, dictionaries, segments and tokens are included. There are no
unaccounted mapping bytes, because no maps are stored.

| Circuit | Current raw / z22 | Whole instances raw / z22 | Shape then instances raw / z22 |
|---|---:|---:|---:|
| MLDSA-44 | 2,670,639 / 959,815 | 6,393,561 / 1,932,323 | 3,220,462 / 1,023,325 |
| MLDSA-65 | 2,896,804 / 989,616 | 7,187,929 / 2,123,663 | 3,556,641 / 1,052,393 |
| mdoc hash, 2 attributes | 548,467 / 100,969 | 960,129 / 178,786 | 553,475 / 102,131 |
| mdoc signature | 222,143 / 63,398 | 236,293 / 68,689 | 222,847 / 64,284 |

Using boundary32 on shape/instance order improves MLDSA to 979,401 / 1,000,657
compressed bytes, but is still worse than current and raises mdoc hash/signature
to 118,703 / 68,856. It is not a common winning policy.

Shape/term/instance with the existing segmenter gives 1,344,693 / 1,401,055
for MLDSA-44/65 and 102,781 / 65,229 for mdoc hash/signature.

Per-layer bipartite shape/instance controls, standard segmentation:

| Circuit | Exclude one/copies: raw / z22 / deltas | Include one/copies: raw / z22 / deltas |
|---|---:|---:|
| MLDSA-44 | 5,323,824 / 1,625,561 / 278,165 | 3,764,858 / 1,167,039 / 192,271 |
| mdoc hash2 | 588,365 / 121,352 / 19,655 | 542,185 / 101,535 / 17,176 |

Including one helps the mdoc hash raw size and distinct-delta count, but not its
zstd-22 size. Neither connectivity rule wins across both applications.

### Independent dictionary-clustering control

As a separate ordinary-LFC2 control, sort delta dictionary entries lexically
within their existing ULEB128-index-width buckets and remap references. This
preserves traversal, IDs, segmentation, dictionary cardinalities, every reference
width and exact raw byte length. No runtime work is added.

| Circuit | Current z22 | Delta dictionary clustering z22 |
|---|---:|---:|
| MLDSA-44 | 959,815 | 918,177 |
| MLDSA-65 | 989,616 | 959,104 |
| mdoc hash2 | 100,969 | 100,150 |
| mdoc signature | 63,398 | 64,442 |

Sorting the segment dictionary too was worse. Delta-only clustering saves
4.3%/3.1% on MLDSA but regresses the combined mdoc archive below. It is retained
as an experiment, not adopted as the shared default.

The actual two-attribute mdoc LFA2 archive, using streaming zstd:

| Policy | Raw | zstd-16 | zstd-22 |
|---|---:|---:|---:|
| Current | 770,782 | 183,465 | 162,101 |
| Whole instances | 1,196,594 | 321,491 | 246,671 |
| Shape then instances | 776,494 | 186,823 | 165,234 |
| Delta dictionary clustering | 770,782 | 190,330 | 163,883 |

These exclude the benchmark container's 32-byte trusted-ID prefix. Individual
compressed circuit sizes must not be added to predict compressed archive size.

The full 52-candidate results, LFC1 controls and delta/segment/token counts are in
[results/template-order-sizes.csv](results/template-order-sizes.csv).
Build/decode times in that sweep are diagnostics only; some size jobs overlapped.

## Geometry and proof implications

| Circuit | Layers | Wires including inputs | Terms |
|---|---:|---:|---:|
| MLDSA-44 | 37 | 3,577,829 | 6,580,787 |
| MLDSA-65 | 37 | 3,756,007 | 7,953,988 |
| mdoc hash2 | 20 | 3,473,933 | 6,394,835 |
| mdoc signature | 21 | 183,618 | 276,481 |

All variants preserve this geometry, original inputs and witnesses. The existing
order-sensitive circuit-ID algorithm is untouched. A traversal change changes
the ID and thus transcript challenges: proof bytes can change slightly through
Merkle multiproof path sharing without a geometry change. Dictionary-only changes
and alternate segmentation of the same traversal preserve the ID and proof.

## Prover/verifier performance

Sequential saved-circuit runs, five repetitions per profile, default allocator,
no overlapping builds or compression. Values are medians; small differences
should not be treated as statistically established speedups.

| Circuit | Policy | Prover ms | Verifier ms | Load + ID ms | Proof bytes |
|---|---|---:|---:|---:|---:|
| mldsa44 | Current | 1076.0 | 650.3 | 177.6 | 665416 |
| mldsa44 | Whole instances | 1086.3 | 651.7 | 181.8 | 665800 |
| mldsa44 | Shape then instances | 1084.8 | 662.5 | 178.7 | 665640 |
| mldsa44 | Delta dictionary clustering | 1060.2 | 646.8 | 178.1 | 665416 |
| mldsa65 | Current | 1190.2 | 722.9 | 213.4 | 719368 |
| mldsa65 | Whole instances | 1181.3 | 728.3 | 218.2 | 718792 |
| mldsa65 | Shape then instances | 1194.5 | 725.7 | 214.3 | 719688 |
| mldsa65 | Delta dictionary clustering | 1196.4 | 727.8 | 215.0 | 719368 |
| mdoc | Current | 337.4 | 181.2 | included | 344236 |
| mdoc | Whole instances | 350.5 | 182.6 | included | 343660 |
| mdoc | Shape then instances | 349.5 | 183.1 | included | 344844 |
| mdoc | Delta dictionary clustering | 342.4 | 185.0 | included | 344236 |

MLDSA prover = commit + prove; load/ID checking, input preparation and proof
serialization/deserialization are excluded from those timers. Verifier is the
numerical core after proof deserialization. The separately timed load includes
one circuit-ID check; an additional untimed check is performed before proving.

mdoc measures the full current two-attribute application flow, including
decompression, circuit decoding, setup and proof serialization. Its trusted
application loader does **not** recompute circuit IDs. It is not comparable to
the MLDSA core-only timer. Current ordinary LFC2 is below the earlier 380 ms target
on this fixture; changing its traversal is unnecessary to reach that target.

All profiles use the same runtime, including the format-independent optimization
from the preceding speed investigation: skip field multiplication by a unit
coefficient in evaluation and dense accumulation. Zero-coefficient assertion
markers still use beta. Do not attribute improvement over older reports solely
to removal of LTP or to traversal.

Every measured proof was serialized, decoded and successfully verified. The
dictionary-only profiles produce byte-identical deterministic proofs to current
LFC2. Whole-instance LFC2 also produces byte-identical proofs to the historical
LTP proofs with that exact traversal: switching representation did not change
the circuit ID or protocol. No proof-size geometry was increased.

Raw timing samples: [results/template-order-timings.csv](results/template-order-timings.csv).

## Actual memory measurements

Separate `bench-memory` build, one proof/verification per fresh process,
`/usr/bin/time -v` for process high-water RSS and a live-allocation tracker for
phase heap peaks. Timing results above do not use this allocation tracker.
Compilation, circuit construction and archive compression are outside these
processes. RSS is the whole process, not a verifier-only peak; heap figures do
not include stacks, executable pages or allocator-retained freed memory.

| Circuit | Policy | Process peak RSS MiB | Prover live heap peak MiB | Verifier live heap peak MiB |
|---|---|---:|---:|---:|
| mdoc | Current | 101.93 | 92.48 | 38.07 |
| mdoc | Whole instances | 103.66 | 93.67 | 39.25 |
| mdoc | Shape then instances | 102.11 | 92.50 | 38.09 |
| mdoc | Delta dictionary clustering | 102.44 | 92.49 | 38.07 |
| mldsa44 | Current | 121.72 | 117.99 | 33.41 |
| mldsa44 | Whole instances | 130.86 | 126.09 | 41.51 |
| mldsa44 | Shape then instances | 122.72 | 119.17 | 34.58 |
| mldsa44 | Delta dictionary clustering | 121.93 | 117.99 | 33.41 |
| mldsa65 | Current | 131.42 | 129.49 | 40.12 |
| mldsa65 | Whole instances | 140.70 | 138.87 | 49.50 |
| mldsa65 | Shape then instances | 132.53 | 130.91 | 41.54 |
| mldsa65 | Delta dictionary clustering | 131.71 | 129.49 | 40.12 |

The MLDSA verifier retains the benchmark's prepared input vector. MLDSA additional
heap over phase entry is unchanged by ordering: 86.10/90.42 MiB for the largest
prover phase and 21.03/24.14 MiB for verification (44/65). Larger total heaps are
therefore resident circuit representation, not additional sumcheck scratch.
Dictionary clustering preserves all vector lengths and has identical tracked
heap usage. Small RSS differences reflect allocator/OS effects.

Exact byte counts and phase-added heap are in
[results/template-order-memory.csv](results/template-order-memory.csv).

## Reproduction

Input files are saved current circuits under `target/traversal-circuits/`, named
`DATASET--kind_abs_lex0213_r5.lfc2`. Datasets measured here are `mldsa44`, `mldsa65`,
`mdoc_hash2` and `mdoc_sig`; this is not a new sweep of all four mdoc attribute counts.

```sh
cargo test --release -p circuits-experimental --test layer_templates --no-run
ORDER_DATASET=mldsa44 ORDER_COMPONENTS=3 ORDER_LOCAL_ORDERS=4 \
ORDER_TRAVERSALS=instances,shape_instances,terms,shape_terms \
ORDER_SEGMENTS=standard,boundary32 ORDER_SAVE_DIR=target/template-order-lfc2 \
cargo test --release -p circuits-experimental --test layer_templates \
  layer_template_order_sweep -- --ignored --nocapture
```

Components 1/2 select bipartite without/with one; component 4 retains the original
traversal and segmentation for the `lex,lexboth` dictionary controls. Component 0
is the fixed-window control. These numeric settings are experiment selectors,
not a production policy.

The saved-circuit proof harness is `tests/template_proofs.rs`, now ordinary LFC2
only. Use `ORDER_PROOF_CIRCUIT`, `ORDER_REPEATS`, `ORDER_SAVE_PROOF` and
`ORDER_EXPECT_PROOF` for MLDSA. For mdoc prepare an archive using `ORDER_SIG`,
`ORDER_HASH`, `ORDER_SAVE_ARCHIVE`; then use `ORDER_MDOC_ARCHIVE` in a fresh process.
Preparation/compression is deliberately outside measured proof processes.

```sh
cargo test --release -p circuits-experimental --test template_proofs --no-run
ORDER_PROOF_CIRCUIT=target/traversal-circuits/mldsa44--kind_abs_lex0213_r5.lfc2 \
ORDER_REPEATS=5 target/release/deps/template_proofs-d8f4deaa5b9e32d4 \
  --ignored --nocapture mldsa44_template_proof

cargo test --release -p circuits-experimental --features bench-memory \
  --test template_proofs --no-run
ORDER_MDOC_ARCHIVE=target/order-mdoc-baseline.archive ORDER_REPEATS=1 \
  /usr/bin/time -v target/release/deps/template_proofs-aeaffcfd5ecda5a8 \
  --ignored --nocapture mdoc_template_proof
```

Executable hashes are from this build; use the paths printed by Cargo when they
change. Invoke the binary directly to exclude Cargo/build memory from RSS.

## Validation completed

- `cargo test --release -p core-proto -p runtime-sumcheck -p runtime-zk`: passed.
- `cargo test --release -p circuits-experimental --test layer_templates --test template_proofs`:
  28 non-ignored tests passed, including exact boundary-segment sharing and
  dictionary remapping across ULEB-width boundaries.
- `cargo check --workspace --all-targets`: passed.
- 52 ordinary-LFC2 candidates passed exact geometry/term/traversal/ID/serialization
  checks. No original input or other wire was renamed.
- 60 timed and 12 fresh memory proof/verification flows passed on MLDSA-44,
  MLDSA-65 and current two-attribute mdoc. These explicitly run the otherwise
  ignored saved-circuit benchmarks.
- No LTP reader, layer storage or runtime dispatch remains; `compute_id` itself
  is unchanged. Previously added opt-in canonical-ID support is preserved.
- `git diff --check`: passed. Unrelated worktree changes were retained.
