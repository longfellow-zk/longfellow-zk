# Per-layer bipartite component layout

2026-09-11. Offline experiment on the same frozen circuits as [the Morton investigation](MORTON_REPORT.md), with MLDSA-44 at period 6.

## Result

The useful common rule is to **include constant-1 in connectivity, order components by their minimum globally distinct vertex ID, and retain Morton traversal within each component**. It improves compressed size on all three fixtures at both zstd-16 and zstd-22. Forward output-wire packing is optional: it helps mdoc further but is slightly worse for MLDSA than grouping terms alone.

Excluding constant-1 and its copies is substantially worse. More components do not necessarily mean more reusable delta sequences. Neither variant approaches 500 kB for MLDSA. This is a promising measured policy, not a completed production scheduler/prover change or evidence about every possible circuit.

Complete segmented LFC2 sizes after zstd-22, in bytes:

| Policy | mdoc signature | mdoc hash | MLDSA-44 p6 |
|---|---:|---:|---:|
| Current global Morton | 117,854 | 161,848 | 2,091,823 |
| Group terms; include 1 | 113,785 | 154,628 | 1,695,604 |
| Group terms; exclude 1 | 267,908 | 695,419 | 4,720,469 |
| Also pack output wires; include 1 | 111,336 | 138,850 | 1,709,103 |
| Also pack output wires; exclude 1 | 195,357 | 701,012 | 3,940,073 |

Grouping alone saves 18.9% for MLDSA relative to the existing segmented LFC2 file. It is one rule across all three fixtures, not a per-application choice between encodings.

## Exact interpretation

For each layer, independently:

1. Construct input vertices `0..ni` and output vertices `ni..ni+no`. Add an undirected edge from each term's output to each of its two operand wires. The two vertex namespaces never alias. Ordinary inputs, including shared original circuit inputs, **do connect components** in this experiment; that differs from the earlier whole-circuit partition.
2. With 1 included, keep every such edge. With 1 excluded, omit edges incident to known constant-1 vertices. Constant-only expressions are evaluated to recognize 1 and every copy of 1; exclusion is not based merely on wire number zero. Other constant values are not excluded. Outputs whose edges disappear still have singleton components and their terms are still emitted. No term is removed.
3. Order components by minimum vertex ID. Since inputs precede outputs in this globally distinct numbering, a component with input edges is ordered by its minimum input ID. Isolated outputs follow connected components. Input-only components with no output terms emit nothing.
4. Emit one component's terms at a time, sorted by the existing absolute Morton `(h0,h1)` comparator, then g, then coefficient bytes. This is component-major traversal, **not** a new global Morton sort and not component-local Morton coordinates.
5. Compute ordinary coordinate deltas and invoke the existing `segment_circuit` unchanged. The result is ordinary LFC2: delta dictionary, reusable segments, and segment tokens. Component maps, bases, and side tables are not added to the file.

The separate output-packing control runs from inputs toward outputs. The previous layer's chosen numbering is retained. After partitioning, pack the current layer's outputs by `(component rank, old output ID)`, then propagate that permutation to both operand references in the next layer. Final external output positions and original circuit input positions remain fixed. Operand pairs are canonicalized after renumbering. Widths, term counts, depth, field, witnesses counts, and padding geometry remain unchanged; there are no gaps or added wires. This is a consistent forward layout, not incompatible independent permutations of both sides of every layer.

## Why the ID convention matters

The initial control compared numeric layer-local IDs on both sides, breaking ties input-before-output. That is a different ordering from distinct vertex IDs: a numerically small output can move its component ahead of one with a smaller input ID. The ambiguity was explicitly tested, not silently changed.

With 1 included and Morton inside components, the mixed-local-ID control gives signature/hash/MLDSA sizes of 117,011 / 155,244 / 1,744,121 bytes at zstd-22. Its signature result regresses 1.4% at zstd-16. The input-first, globally distinct convention in the main table avoids that regression and is more natural for a graph with disjoint vertex namespaces. Output packing under mixed-local-ID ordering also regresses both mdoc fixtures. Thus the convention is part of the policy, not an implementation detail to leave unspecified.

The initial controls also tested both lexicographic orientations inside components. Neither supplied a shared improvement across all three fixtures. All controls, including output-packing followed by global Morton, are retained in [the full size table](BIPARTITE_DATA.md).

## Causal observations

Including 1 leaves the first layer as **one component in every fixture**. Its existing term order and output numbering therefore remain unchanged in the main policies. This protects the very large first layer of mdoc hash (3,175,962 terms) and MLDSA (2,267,869 terms). This behavior follows from connectivity, not an explicit first-layer exception.

The gains occur in later layers, with nonuniform results. Under globally distinct ordering plus output packing, independently zstd-16-compressing each segmented layer body gives:

| Circuit / input-first depth | Original deltas | Include 1 | Exclude 1 | Original compressed body | Include 1 | Exclude 1 |
|---|---:|---:|---:|---:|---:|---:|
| mdoc hash / 2 | 983 | 418 | 70,368 | 10,943 | 4,209 | 267,800 |
| MLDSA / 2 | 2,297 | 2,569 | 49,245 | 28,012 | 17,790 | 208,314 |
| MLDSA / 10 | 5,712 | 4,192 | 14,657 | 61,366 | 32,267 | 65,132 |
| MLDSA / 18 | 4,902 | 8,160 | 88,612 | 55,052 | 78,200 | 398,924 |

Independent body compression diagnoses layers; these values do not add up to whole-file zstd size because the latter shares history across layers.

Removing 1 splits MLDSA layer 18 from one component into **43,618**. In the packed, input-first control, that layer introduces 47,323 distinct interior delta tuples absent from the original layer, plus 41,285 new tuples occurring only at component starts. For mdoc hash layer 2, 70,013 new tuples occur only at component starts, versus only 283 new interior tuples. The regression therefore has concrete sources: expensive transitions between fragments, and changed consecutive terms inside fragments. It is not merely the overhead of a component table—there is no such table.

Including 1 keeps constant-linked copy/linear work together and avoids this fragmentation. Morton within components retains two-coordinate locality. Nevertheless, not every layer improves, as MLDSA layer 18 shows; forward packing can disturb the predecessor numbering even when the current layer is one component. These observations support including 1 for this policy, not a claim that 1 should always be a connectivity edge in every compiler algorithm.

Distinct global tuples also are not the whole objective. Grouping with 1 changes signature/hash/MLDSA global counts from 14,192 / 18,449 / 174,923 to 14,646 / 18,994 / 159,372. Both mdoc files get smaller despite slightly more distinct tuples, because sequence/segment repetition matters too.

## LFC2 memory and decoding

The compact representation is retained on disk and in memory; no template expansion or resegmentation occurs during decoding.

| Circuit | Original compact payload estimate | Group/include 1 | Pack/include 1 |
|---|---:|---:|---:|
| mdoc signature | 929,920 | 885,636 | 924,228 |
| mdoc hash | 2,069,548 | 1,976,476 | 1,916,024 |
| MLDSA | 15,216,960 | 12,446,984 | 12,470,312 |

Estimates include delta payloads, segment entries/tokens, and 64-bit Vec headers for segments. They exclude spare capacity, allocator overhead, constants and geometry. The logs contain decompression + LFC2 reading + ID timing observations. These were median-of-three measurements with other experiments running concurrently, so they are not controlled speed comparisons.

## Correctness, proof implications, and scope

For every variant, re-sort the terms into canonical Morton order (and undo the wire permutation for packed variants) and assert exact original LFC1 equality. Also read each produced segmented LFC2 file using the existing reader with circuit-ID enforcement, then assert exact equality with the corresponding reordered LFC1 file. All 42 variant checks across 12 fixture runs passed. Four additional layer-diagnostic runs passed. Five graph unit tests passed in both test packages (15 executions because the mdoc harness includes the module twice). `git diff --check` passed.

No production scheduler or runtime code was changed. The pre-existing scheduler and its component-size majority switch remain frozen, not endorsed as a final policy. No compress-both-and-pick rule or application-specific threshold is introduced by these experiments.

Non-global-Morton traversal still needs runtime ordering/folding support. The circuit ID changes, since the existing ID includes term order and wire labels. Sorting and packing do not add witnesses or sumcheck rounds, but no new prover/verifier or actual proof-size benchmark was implemented here. Packed variants additionally require consistent permutation of internal witness positions. Therefore unchanged proof bytes or measured proving speed are **not** claimed.

## Reproduction and logs

```
MORTON_BIPARTITE_ONLY=1 BIPARTITE_INPUT_FIRST=1 cargo test -p mdoc-zk-circuits analyze_signature_morton -- --ignored --nocapture
MORTON_BIPARTITE_ONLY=1 BIPARTITE_INPUT_FIRST=1 cargo test -p mdoc-zk-circuits analyze_hash_morton -- --ignored --nocapture
MORTON_BIPARTITE_ONLY=1 BIPARTITE_INPUT_FIRST=1 cargo test -p circuits-experimental analyze_mldsa44_morton -- --ignored --nocapture
```

Add `BIPARTITE_PACK_OUTPUTS=1` for forward output packing. Add `BIPARTITE_STATS_ONLY=1` for per-layer diagnostics instead of whole-file sizes. Omit `BIPARTITE_INPUT_FIRST` for the initial mixed-local-ID controls and the additional intra-component ordering comparisons.

- Main grouping: [signature](results/bipartite-inputfirst-signature.log), [hash](results/bipartite-inputfirst-hash.log), [MLDSA](results/bipartite-inputfirst-mldsa.log).
- Main packing: [signature](results/bipartite-inputfirst-packed-signature.log), [hash](results/bipartite-inputfirst-packed-hash.log), [MLDSA](results/bipartite-inputfirst-packed-mldsa.log).
- Main packed layer diagnostics: [hash](results/bipartite-inputfirst-packed-stats-hash.log), [MLDSA](results/bipartite-inputfirst-packed-stats-mldsa.log).
- Mixed-local-ID grouping: [signature](results/bipartite-signature.log), [hash](results/bipartite-hash.log), [MLDSA](results/bipartite-mldsa.log).
- Mixed-local-ID packing: [signature](results/bipartite-packed-signature.log), [hash](results/bipartite-packed-hash.log), [MLDSA](results/bipartite-packed-mldsa.log).
- Mixed-local-ID layer diagnostics: [hash](results/bipartite-stats-hash.log), [MLDSA](results/bipartite-stats-mldsa.log).
