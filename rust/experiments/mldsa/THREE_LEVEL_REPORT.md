# Re-Pair with three-level segmentation

## Result

The additional level improves **raw storage**, but none of the tested three-level
variants beats the best existing flat-LFC2 zstd results. There is no reason from
these measurements to adopt the format for the compressed-size objective.

Tested **52 seed/policy combinations on four circuits**: 208 fully checked circuit
outputs and 52 actual combined mdoc archive measurements. All tests use the same
wire numbering, term order, geometry, witnesses, field serialization, and circuit IDs
as the preceding flat-LFC2 experiment.

This is a bounded three-level representation, not an arbitrary-depth Re-Pair grammar.

## Representation

The experimental magic is `L3E1`. The circuit header, coefficients, widths, delta
tables, and final circuit ID have the same encoding as LFC2. Each layer contains:

1. The existing delta dictionary: exact `(dg, dh0, dh1, coefficient-index)` tuples.
2. A lower segment dictionary: flat lists of delta IDs.
3. An upper segment dictionary: flat lists of lower-segment IDs.
4. An execution stream of upper-segment IDs.

Both dictionary counts, every body length, every reference, and the final execution
stream are serialized with the existing ULEB convention. All overhead is included
in the reported bytes. There are no same-level references, recursive rules, external
maps, or uncounted dictionaries. The maximum segment-reference nesting is two.

Execution is three nested loops: execution reference -> upper body -> lower body ->
delta. No sorting or hash table is needed to iterate the decoded representation.
The offline Re-Pair builder still uses occurrence sets and a priority queue.

## Constructions tested

Four starting LFC2 segmentations were used:

- `reuse`: selected template-interior reuse baseline.
- `cdc`: CDC-128 residual segmentation plus template-interior reuse.
- `pruned`: the previous pruned delta Re-Pair-512 flat result.
- `factored`: CDC/reuse with prefix/suffix-8 factoring and bucketed suffix ordering.

For each seed:

- **Top-level Re-Pair:** retain the flat segment bodies and parse their execution
  references into upper segments. Caps 8, 64, and 512 lower references; also a
  pruned cap-64 variant and a bucketed suffix-ordering variant.
- **Dictionary factoring:** run Re-Pair across the *stored* flat dictionary bodies,
  splitting each original body into shared lower segments. The old bodies become
  upper segments, and the original execution stream is retained. Unique separator
  symbols prohibit matches crossing original body boundaries; they are checked and
  removed before serialization. Caps 8, 32, 128, and 512 deltas, plus pruning and
  suffix-ordering variants. Candidate counts here are stored-body occurrences,
  not counts weighted by how often the original segment executes.

Additionally, four **two-pass constructions** start from the full delta execution
stream: lower Re-Pair cap 32 or 128, then upper Re-Pair cap 8 or 128, with pruning
at both stages. Caps are measured in the symbols of the corresponding stage.

Dead bodies are removed and both dictionary reference spaces are frequency-ranked.
Suffix variants cluster within ULEB-width buckets. The temporary pair grammar is
flattened only into its corresponding stage's alphabet, not all the way to deltas
when producing upper bodies. No per-circuit size chooser was installed.

## Sizes

Cells are **raw / zstd-22 bytes**. mdoc is the actual joint LFA2 archive, not the sum
of standalone compressed circuits. LFA2 metadata, both payloads, and IDs are included.
Standalone circuits use bulk zstd; archives use the existing streaming compressor.

| Policy | MLDSA44 | MLDSA65 | mdoc archive |
|---|---:|---:|---:|
| Flat CDC/reuse | 2,030,895 / 363,275 | 2,205,120 / 369,259 | 1,009,975 / 146,340 |
| Flat CDC/reuse, bucketed suffix order | 2,030,895 / 351,999 | 2,205,120 / 358,593 | 1,009,975 / 151,234 |
| Flat pruned delta Re-Pair | 942,255 / 371,594 | 997,577 / 375,943 | 421,936 / 159,472 |
| Three-level top Re-Pair-64, pruned, CDC seed | 2,027,942 / 364,979 | 2,198,978 / 372,101 | 989,780 / 147,303 |
| Three-level top Re-Pair-64, suffix order, CDC seed | 2,029,226 / 354,961 | 2,201,980 / 362,292 | 990,675 / 152,082 |
| Three-level dictionary Re-Pair-128, pruned, CDC seed | **821,662 / 399,224** | **859,157 / 405,844** | 438,494 / 175,843 |
| Three-level two-pass 32/128, pruned | 844,809 / 400,126 | 910,189 / 403,292 | **366,057 / 164,745** |

The best three-level compressed results in this sweep are:

- MLDSA44: **354,961** bytes, versus the preceding flat minimum **349,727**.
- MLDSA65: **362,292** bytes, versus the preceding flat minimum **356,269**.
- mdoc archive: **147,303** bytes, versus the preceding flat minimum **145,818**.

These individual minima use different policies. Best standalone three-level mdoc
signature/hash2 sizes are 54,986 / 93,348 bytes; these do not determine the joint
archive size by summation. Every raw and zstd-16/22 measurement is in the CSVs.

## What the control shows

An independent Python parser checked that `cdc/top_64_suffix` has exactly the same
delta-table bytes and lower dictionary as the preceding flat
`dictbucketsuffix@reuse_cdc_128` circuit, and that expanding its upper references
reproduces exactly the flat circuit's lower-reference execution sequence.

Thus the comparison isolates the extra reference level and its encoding, rather
than attributing a dictionary-ordering benefit to three-level segmentation:

- MLDSA44 raw saves **1,669** bytes, but zstd grows **2,962** bytes.
- MLDSA65 raw saves **3,140** bytes, but zstd grows **3,699** bytes.
- mdoc archive raw saves **19,300** bytes, but zstd grows **848** bytes.

Factoring dictionary bodies attacks a much larger raw target. For CDC-seeded
MLDSA44, the original 1,181,739 stored delta references become 122,779 lower delta
references plus 158,385 upper references; the 15,629 execution references remain.
Raw bytes fall from 2,030,895 to 821,662, but zstd rises from 363,275 to 399,224.

The observed trade-off is that explicit factoring replaces redundant sequences with
reference streams and extra dictionary boundaries. On these fixtures, zstd handles
the original redundancy better than the resulting representation. The measurements
do not establish that every possible three-level parse must lose, or that a fully
recursive grammar would behave the same way.

## Time and runtime implications

Release/native sweep timings below are incremental on already-segmented saved
fixtures; they exclude construction of the seed, serialization, verification, and
zstd. Jobs ran concurrently, so these are indicative rather than isolated benchmarks.

| Extra segmentation work | MLDSA44 | MLDSA65 | mdoc signature | mdoc hash2 |
|---|---:|---:|---:|---:|
| Top Re-Pair-64 + suffix ordering | 6.0 ms | 5.9 ms | 0.6 ms | 7.0 ms |
| Dictionary factoring-128, pruned | 482 ms | 516 ms | 50 ms | 186 ms |
| Two full-stream passes, 32/128, pruned | 2,536 ms | 2,983 ms | 86 ms | 2,123 ms |

The top-level pass is cheap because it operates on thousands of references, not
millions of deltas. Factoring visits stored dictionary bodies once rather than all
their execution instances. The two-pass construction still pays for a full
delta-level Re-Pair pass.

A direct nested-iteration checksum microbenchmark was also run, without flattening:
CDC-seeded MLDSA44 took 4.93 ms for the top-level representation and 5.70 ms for the
factored representation, versus 4.81 ms for the flat seed. MLDSA65 took 6.17 / 6.62 ms
versus 5.69 ms. These are **not prover timings**: arithmetic, memory allocation, and
the prover's own term processing can change the impact. Reader allocation times are
also recorded in the CSVs; neither those times nor raw bytes are peak-memory results.

## Validation and scope

- 208 circuit cases passed strict expanded-delta equality, exact experimental-format
  read/write round-trip, conversion to LFC2, and the production reader's circuit-ID
  check. The original metadata and coefficient encodings are preserved verbatim.
- Five unit tests passed, including the pair/recount reference tests, empty layers,
  deterministic builds, and boundary-separated factoring. Two offline tests are
  ignored by the ordinary unit run.
- Nine full proof/verifier flows passed across three representative policies on
  MLDSA44, MLDSA65, and mdoc. **The test adapter flattened L3E1 to LFC2 first.**
  These produced byte-identical baseline proofs: 218,708 / 227,852 / 343,436 bytes.
- The production prover does **not** read L3E1 directly. This experiment implements
  a trusted offline reader and direct iterator, not a hardened runtime-format change.
  Direct prover support would require exposing the additional lookup/loop through
  circuit iteration; the mathematical circuit and transcript need not change.
- No production default, prover/verifier implementation, circuit source, or C++ file
  was changed. The only change to the previous pair implementation is a reusable
  integer-stream entry point used by this experiment.

## Files and reproduction

- `circuits/experimental/tests/three_level_segments.rs`: format, builders, iterator,
  reader, reconstruction checks, and archive harness.
- `run_three_level.py`: four seeds, 52 combinations, release-binary snapshot and
  manifest, full raw/zstd measurements, and actual archives.
- `validate_three_level.py`: nine proof-equivalence checks through the flat adapter.
- `report_three_level.py`: tables and independent dictionary-order control.
- [Exact size tables](results/three-level-tables.md)
- [All 208 circuit measurements](results/three-level-circuits.csv)
- [All 52 policies with joint mdoc archive sizes](results/three-level-shared.csv)
- [Dictionary-order control assertions](results/three-level-controls.json)

Build with `cargo test --release -p circuits-experimental --features
mldsa-slicing-experiment --test three_level_segments`. Run the Python runner's
`run`, `summary`, and `archives` phases, using a fresh `--root` if the executable
changes. Recorded artifacts, executable snapshot, and logs are in
`target/three-level-v1`; validation logs are in its `validation` directory.
