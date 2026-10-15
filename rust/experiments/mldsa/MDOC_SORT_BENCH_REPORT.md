# mdoc current: comparison-sort compatibility benchmark

## Result

The straightforward duplicate-allowing implementation works, but the new term order makes proving about 49% slower and verification about 104% slower on the actual current mdoc benchmark. Prover peak additional heap rises about 18%; verifier peak additional heap rises about 72%.

This is `mdoc_zk_bench_current`, CURRENT_VERSION 8, two disclosed attributes, both signature and hash circuits in the end-to-end flow. It is not the earlier standalone offline-analysis fixtures.

| Metric | Original Morton, original path | Type/output-major + comparison sort/merge | Change |
|---|---:|---:|---:|
| Prover time | 400.923 ms | 598.711 ms | +49.3% |
| Verifier time | 186.217 ms | 380.477 ms | +104.3% |
| Prover peak additional heap | 95989466 bytes (95.99 MB) | 113165686 bytes (113.17 MB) | +17.9% |
| Verifier peak additional heap | 40651756 bytes (40.65 MB) | 69911672 bytes (69.91 MB) | +72.0% |
| Circuit archive, zstd-16 | 319179 bytes | 183465 bytes | -42.5% |
| Circuit archive, before zstd | 973985 bytes | 770782 bytes | -20.9% |
| Deterministic proof bytes | 343596 | 344076 | +480 bytes |

Time is the median of three independent process-level Criterion mean estimates. Each process ran 10 measured prover calls and 10 measured verifier calls, with the benchmark's existing 100 ms requested warm-up/measurement settings (Criterion automatically used longer collection times because each invocation exceeds 100 ms). Runs alternated baseline/modified and did not overlap. All dry-run proofs verified and all measured verification calls accepted.

Memory uses the benchmark's existing allocation tracker: peak live heap during the operation minus live heap immediately before it. It is **not process RSS**, and excludes already-resident setup allocations. It includes circuit decompression and the temporary per-layer sorting buffers. Memory peaks were identical across all three repeats of each main mode. MB is decimal.

Compilation, experimental circuit reordering, archive construction and initial diagnostic decoding occurred before timing and before per-operation peak resets. The OS process HWM includes the much larger compiler/setup phase, so it is not used as the prover/verifier memory figure.

## What changed

- In `runtime/sumcheck/src/hquad.rs`, the opt-in `LFZK_HQUAD_SORT=1` path builds weighted HQuad entries exactly as before, including nonadjacent duplicates.
- It comparison-sorts a u32 index permutation by Morton pair order, applies that permutation in place to the existing corner/value arrays, and merges adjacent equal pairs by field addition.
- There is **no radix sort, no hash table and no binary search per term**. Field-valued duplicate entries are allowed. Sorting happens once per layer per operation, not once per sumcheck round.
- Already strictly Morton-ordered unique corners return through a fast path without allocating a permutation.
- The shared helper is used by both prover and verifier. Direct-streaming verifier evaluation was deliberately not implemented, so the main comparison measures the same straightforward adaptation on both sides.
- `MDOC_BENCH_KIND_ORDER=1` changes benchmark setup only: classify terms into constant/linear/square/product groups, then sort by g descending, h1 descending, h0 ascending, coefficient bytes. It is the same policy as `kind_abs_lex0213_r5`.
- The term multiset and all wire IDs are unchanged; the helper checks exact restoration to the original canonical term lists. Stock segmentation and LFC2 decoding are unchanged. Reordered LFC2 files are checked with circuit-ID verification and exact serialization equality before benchmarking.
- New circuit IDs and the benchmark-only archive/spec ID are computed consistently. Proof geometry and input/witness layout do not change, but proof bytes need not be identical because circuit IDs bind the transcript.
- Both switches default off. The production scheduler and circuit-generation defaults were not changed by this work; unrelated preexisting workspace changes were preserved.

The implementation sorts the existing structure-of-arrays through an index permutation rather than allocating another full array of field-valued records. It still retains duplicate entries during construction and retains their vector capacity after merging. The extra live entries and sorting index are real working-memory costs included above.

## Control: support enabled, original circuits unchanged

One additional fresh-process control used `LFZK_HQUAD_SORT=1` with the original Morton circuits:

- Prover: 401.892 ms.
- Verifier: 188.603 ms.
- Prover peak additional heap: 95989466 bytes.
- Verifier peak additional heap: 40651757 bytes.

This control takes the already-sorted fast path. It is one run, not another three-run aggregate. The major slowdown in the main comparison comes from consuming the new order, not merely enabling support for it.

## Individual runs

| Mode | Run | Prover mean (ms) | Verifier mean (ms) | Prover peak (bytes) | Verifier peak (bytes) |
|---|---:|---:|---:|---:|---:|
| baseline | 1 | 398.939 | 185.743 | 95989466 | 40651756 |
| baseline | 2 | 400.923 | 186.625 | 95989466 | 40651756 |
| baseline | 3 | 401.305 | 186.217 | 95989466 | 40651756 |
| reordered | 1 | 605.361 | 384.197 | 113165686 | 69911672 |
| reordered | 2 | 591.493 | 376.059 | 113165686 | 69911672 |
| reordered | 3 | 598.711 | 380.477 | 113165686 | 69911672 |

Criterion estimates and their per-run 95% confidence intervals are recorded in [the machine-readable summary](results/mdoc-duplicates-summary.json). Raw benchmark logs are in `results/mdoc-duplicates-{baseline,reordered}-{1,2,3}.log`; the control is [here](results/mdoc-duplicates-morton-control.log).

## Circuit geometry and environment

Both modes:

- Hash: 77785 inputs, 1035 public inputs, 16 outputs, 3396148 wires, 6394835 terms, 20 layers; encoded block size 5246.
- Signature: 3941 inputs, 707 public inputs, 6 outputs, 179677 wires, 276481 terms, 21 layers; encoded block size 4445.
- Ligero rateinv 7, nreq 132, unchanged.
- AMD Ryzen 9 9950X, 16 cores / 32 logical CPUs.
- Rust 1.97.1 (8bab26f4f 2026-07-14); optimized bench profile, opt-level 3, LTO, one codegen unit.
- Existing worktree based on commit fa578cc5bb055d72df379dc195393ea2f124788e; this was not a clean-commit comparison.
- Same optimized binary for all modes. No CPU affinity or frequency lock was applied.

## Validation and reproduction

`cargo test -p runtime-sumcheck` passed all 12 tests both with and without `LFZK_HQUAD_SORT=1`. New tests exercise nonadjacent duplicate accumulation, permutation cycles, idempotence, subsequent hand folding, cancellation to a zero corner, and empty/singleton normalization. The mdoc benchmark exercises the complete P256 and GF2 proof/verifier paths. `git diff --check` passed.

```sh
cargo bench -p mdoc-zk-runtime --bench mdoc_zk_bench_current --no-run

env -u MDOC_BENCH_KIND_ORDER -u LFZK_HQUAD_SORT \
cargo bench -p mdoc-zk-runtime --bench mdoc_zk_bench_current -- --noplot

MDOC_BENCH_KIND_ORDER=1 LFZK_HQUAD_SORT=1 \
cargo bench -p mdoc-zk-runtime --bench mdoc_zk_bench_current -- --noplot
```

For the recorded runs, the resulting executable was invoked directly with `--bench --noplot --save-baseline dup-MODE-RUN`, sequentially baseline-1, reordered-1, baseline-2, reordered-2, baseline-3, reordered-3.
