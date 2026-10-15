# Round-major HQuad preparation: sorting experiment

Historical experiment: prover-side sorting was subsequently removed at the
user's request. Round-major now requires already-Morton-ordered circuit terms;
hand-major still accepts arbitrary traversal. The implementations and results
below are retained as offline experimental data, not the current runtime policy.

## Decision

Use precomputed Morton keys, standard unstable comparison sorting of
`(key, original_index)` records, and one sequential gather/coalescing pass into
exactly-sized coordinate and weight arrays. This is `index-key-gather-tight` in
the experiment. It replaces the old in-place permutation cycles in
`runtime/sumcheck/src/hquad.rs`.

This is a speed-first choice, **not** the lowest-memory candidate. It won the
mdoc hash, mdoc signature, and MLDSA-44 measurements. On MLDSA-65 it was within
0.2 ms (0.1%) of the otherwise identical non-tight gather, while allocating far
less memory. There is one runtime policy for all circuits and fields, with the
existing no-sort fast path for already-Morton pairs. No trial-and-pick policy,
radix sort, or hash table was added to the prover.

The compiler traversal, stored LFC1/LFC2 data, segmentation, wire numbering,
circuit IDs, witnesses, and proof protocol are unchanged. Hand-major proving is
unchanged. Only round-major working-state preparation changes.

## Why this won

- Sorting coordinates directly recomputes the Morton comparison and follows
  indirect coordinate reads repeatedly. Precomputing each 64-bit Morton key
  converts the sort comparisons to integer comparisons.
- Sorting weighted records directly moves field-valued data repeatedly.
  Sorting compact key/index records avoids those movements.
- The previous permutation cycles perform scattered swaps in both arrays.
  Gathering reads each source once and writes outputs sequentially, coalescing
  duplicates as it goes.
- Counting distinct sorted keys before allocation avoids retaining space for
  already-coalesced pairs throughout subsequent sumcheck rounds.

Compact raw-term sorting before field weighting was the lowest-memory serious
contender. It loses some speed because it sorts all terms, whereas weighted
preparation first coalesces adjacent equal pairs, and because field weighting
then accesses g bindings in sorted rather than stored order. The timings below
measure that complete preparation, not sorting alone.

## Preparation timings

Milliseconds summed over all layers; median of three repetitions. Real stored
current circuits, deterministic full-field equality-table bindings, and the same
bindings held fixed for all candidates. Candidate execution order rotates by
layer and repetition. Circuit decoding, equality-table construction, reference
preparation, result checking, and destruction are outside the timed region.
Timing runs use the system allocator, without allocation tracking.

Every candidate's corner sequence and every field-valued weight were checked
against the existing implementation for every layer, including nonadjacent
duplicates. The final lazy-key refinement used five repetitions.

| Candidate | mdoc hash (2 attrs) | mdoc signature | MLDSA-44 | MLDSA-65 |
|---|---:|---:|---:|---:|
| index-cycle | 339.98 | 13.14 | 505.63 | 709.44 |
| index-gather | 171.88 | 11.81 | 286.02 | 342.59 |
| weighted-coordinates | 185.42 | 13.62 | 291.16 | 348.66 |
| weighted-key | 146.98 | 9.67 | 205.85 | 260.58 |
| weighted-key-stable | 150.92 | 9.64 | 238.26 | 305.73 |
| raw-coordinates | 208.01 | 11.34 | 298.20 | 344.84 |
| raw-key | 143.88 | 8.41 | 181.03 | 223.79 |
| raw-key-stable | 156.06 | 9.01 | 208.96 | 254.15 |
| raw-packed | 152.14 | 8.36 | 201.61 | 256.96 |
| soa-quicksort | 347.39 | 13.56 | 394.49 | 481.02 |
| index-key-gather | 109.95 | 8.29 | 173.47 | 215.71 |
| raw-key-tight | 145.99 | 8.46 | 187.56 | 229.48 |
| raw-key-stable-tight | 156.11 | 9.02 | 208.20 | 256.55 |
| raw-key-grouped | 141.74 | 8.31 | 184.52 | 222.61 |
| index-key-gather-tight | 107.00 | 8.12 | 171.45 | 215.89 |
| weighted-indirect | 113.25 | 8.20 | 176.26 | 226.57 |
| raw-ranges | 126.76 | 8.27 | 198.01 | 239.67 |
| weighted-indirect-lazy-key | 134.59 | 8.48 | 178.76 | 229.33 |

Candidate descriptions:

- `index-cycle`: previous implementation, coordinate comparator and in-place
  permutation cycles.
- `index-gather`: same comparator, sequential gather instead of cycles.
- `weighted-coordinates`: sort weighted coordinate records directly, coalesce,
  then convert to the existing parallel-array representation.
- `weighted-key[-stable]`: same with precomputed keys; unstable/stable sorting.
- `raw-coordinates`: sort unweighted g/h/coefficient-index records.
- `raw-key[-stable]`: sort 16-byte key/g/coefficient-index records.
- `raw-packed`: sort packed 128-bit key/g/coefficient-index records.
- `soa-quicksort`: safe lockstep paired introsort with insertion-sort and
  heapsort fallbacks, retaining parallel arrays.
- `index-key-gather`: precomputed keys and gather, without tight output sizing.
- `*-tight`: count unique pairs and allocate exactly the required output size.
- `raw-key-grouped`: additionally decode Morton coordinates only for new groups.
- `weighted-indirect`: omit the initial coordinate array; reconstruct output
  coordinates from keys after gathering weights.
- `raw-ranges`: collect consecutive equal-pair ranges, sort those ranges, then
  weight and coalesce.
- `weighted-indirect-lazy-key`: additionally compute keys only for new adjacent
  groups.

## Peak preparation allocation

Peak additional live Rust heap, excluding the preexisting circuit, bindings,
reference result, and witnesses. Allocation tracking was enabled in separate
runs. These are **not** full-prover peaks or RSS.

| Candidate | mdoc hash MiB | MLDSA-44 MiB | MLDSA-65 MiB |
|---|---:|---:|---:|
| index-cycle | 57.06 | 81.73 | 127.84 |
| weighted-key | 78.43 | 75.92 | 114.92 |
| raw-key-grouped | 62.74 | 45.14 | 65.78 |
| index-key-gather-tight | 92.70 | 108.61 | 166.05 |

The selected policy increases temporary peak allocation. Its retained quad is
smaller: mdoc hash 44,875,584 → 22,407,336 bytes; MLDSA-44
68,558,112 → 11,049,088 bytes; MLDSA-65 107,242,912 → 13,256,032 bytes.
There is no claim that this peak-memory tradeoff is free.

## End-to-end results

### Current mdoc (two disclosed attributes)

Same v8 benchmark flow and identical stored circuits, selecting only the sumcheck
schedule in a temporary copy of the application wrappers. Proving includes
decompression, witness preparation, commitments, proofs, and serialization;
verification includes decompression and parsing. Compilation is outside these
measurements. Each Criterion run used ten samples, three seconds of measurement,
and one second of warmup. Round-major entries are medians of three runs before
and after. The new hand-major control is one run (old control: three runs).

| Schedule / preparation | Prover ms | Verifier ms | Prover peak heap MiB | Proof bytes |
|---|---:|---:|---:|---:|
| Round-major, previous cycles | 752.82 | 201.04 | 115.06 | 344,076 |
| Round-major, selected gather | 503.20 | 198.76 | 150.69 | 344,076 |
| Hand-major, previous control | 392.02 | 201.69 | 92.29 | 344,236 |
| Hand-major, new control | 392.55 | 199.67 | 92.29 | 344,236 |

Round-major proving improves by 33.2%, with a 31.0% higher temporary prover heap
peak. The default hand-major path remains unchanged. Verifier peak additional
heap is 37.53 MiB for either schedule. Heap measurements exclude preexisting
allocations and are not process RSS. These end-to-end mdoc runs retain the
benchmark's tracking allocator, unlike the uninstrumented preparation sweep.

The combined circuit archive remains 770,782 bytes, or 183,465 bytes with zstd
level 16. Its ID remains
`4bba6d33dd704c8b54aa51206203ad4b7f6db7d2d3e5c4e4e0be8eea774e2198`.
Proof lengths differ between schedules, but not between sorting implementations
within either schedule.

Logs: [before](results/hquad-mdoc-before.md),
[round-major 1](results/hquad-mdoc-round-after-1.log),
[round-major 2](results/hquad-mdoc-round-after-2.log),
[round-major 3](results/hquad-mdoc-round-after-3.log),
[hand-major control](results/hquad-mdoc-hand-after.log).
The same temporary harness used for both measurements is at
`/tmp/mdoc-dual-bench.qFvFhT`; it depends on the workspace runtime crates and
selects the wrapper schedule with `MDOC_SUMCHECK_ORDER`.

### MLDSA (period 6, round-major)

Single uninstrumented end-to-end smoke measurements, not statistical medians.
Unlike the full mdoc flow, this benchmark times commitment separately from
proving. All generated proofs verified, including serialized-proof roundtrips.

| Circuit | Previous prove ms | Selected prove ms | New commit ms | Previous verify ms | New verify ms | Proof bytes |
|---|---:|---:|---:|---:|---:|---:|
| MLDSA-44 | 1,513.36 | 1,171.68 | 251.24 | 677.45 | 670.85 | 665,896 |
| MLDSA-65 | 1,729.41 | 1,263.55 | 274.56 | 750.14 | 761.47 | 718,920 |

Separate allocation-tracked runs measured the selected implementation:

| Circuit | Prove-phase peak additional bytes | Commit + prove peak additional bytes | Verify peak additional bytes |
|---|---:|---:|---:|
| MLDSA-44 | 124,649,272 | 146,828,880 | 22,056,184 |
| MLDSA-65 | 186,702,040 | 212,689,032 | 25,316,376 |

The combined peak uses the precommit baseline and includes retained commitment
state; the prove-only peak uses the preprove baseline. No matched old full-prover
MLDSA memory run was taken here; the preparation table above provides the
matched old/new preparation comparison.

Circuit geometry and serialized sizes are unchanged:

| Circuit | Wires | Terms | Layers | LFC1 bytes | LFC1 zstd-16 | LFC2 bytes | LFC2 zstd-16 |
|---|---:|---:|---:|---:|---:|---:|---:|
| MLDSA-44 | 3,449,557 | 6,580,787 | 37 | 78,996,522 | 669,700 | 2,670,639 | 997,383 |
| MLDSA-65 | 3,599,744 | 7,953,988 | 37 | 95,475,126 | 861,477 | 2,896,804 | 1,031,363 |

This runtime preparation optimization does not advance the separate 500 KB
compressed-circuit target. Circuit IDs remain
`1c882777f206c0cf031a2a26ede3b17de2a5b1730ec3cf6d74a5cf62bff12e5f`
(44) and
`a7738549223e481d6651e22881c90bc0f6331d6b7cabb8f60afbff45bb76caa8`
(65).

Logs: [before](results/hquad-mldsa-before.log),
[after timing](results/hquad-mldsa-after-time.log),
[after memory](results/hquad-mldsa-after-memory.log).

## Validation

- Runtime sumcheck and ZK tests: 22 passed, including arbitrary LFC1/LFC2
  traversal, multiple fields, full-width Morton keys, empty inputs, wrong
  schedules/tampering, and legacy RFC byte-for-byte checks.
- Current and historical mdoc release integration tests: four passed
  ([log](results/hquad-mdoc-tests.log)).
- Both MLDSA proof benchmarks passed with and without allocation tracking.
- All 18 preparation candidates matched every reference corner and field
  weight on every layer of all four circuits; paired-sort/key unit tests passed.
- `cargo check --workspace --all-targets` passed.
- Strict Clippy passed for runtime-sumcheck/runtime-zk and for the new experimental
  test with `--no-deps`. Broader experimental dependency linting encounters the
  preexisting `byte_char_slices` warning in mdoc hash constants; that unrelated
  file was left unchanged.

## Reproduce

Run from the Rust workspace root with the saved circuit files under
`target/traversal-circuits`:

```sh
cargo test -p circuits-experimental --release --test hquad_sort hquad_preparation_sweep -- --ignored --nocapture --test-threads=1
HQUAD_REPEATS=1 cargo test -p circuits-experimental --release --features bench-memory --test hquad_sort hquad_preparation_sweep -- --ignored --nocapture --test-threads=1
```

Optional controls: `HQUAD_DATASET`, `HQUAD_CANDIDATE`, `HQUAD_REPEATS`,
and `HQUAD_CIRCUIT_DIR`. These are offline test controls, not runtime policy
switches. The test reads `{dataset}--kind_abs_lex0213_r5.lfc2` with ID checking.

Full data: [CSV](results/hquad-preparation.csv),
[timing log](results/hquad-preparation-time.log),
[memory log](results/hquad-preparation-memory.log),
[lazy-key refinement](results/hquad-preparation-lazy-key.log).
