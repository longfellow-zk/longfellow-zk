# Dual sumcheck schedule validation

The existing compiler traversal and dense hand-major default are unchanged.
`ZkProver` and `ZkVerifier` expose
`.with_sumcheck_order(runtime_zk::SumcheckOrder::RoundMajor)` to select the
legacy interleaved protocol. Both peers must select the same trusted schedule.
The normal and symbolic sumcheck verifiers use that schedule.

Either mode accepts arbitrary stored term traversal. Round-major proving forms
the g-bound weighted pairs, skips sorting if already Morton ordered, otherwise
comparison-sorts an index permutation, permutes the working arrays in place,
and combines duplicate pairs. It then uses the legacy sparse hand binding.
There is no radix sort or runtime hash table. The stored circuit, wire IDs,
segmentation, and circuit ID are not modified. The verifier does not sort.
This is compatibility support, not a dense interleaved-prover optimization.

## Validation

- `cargo test -p runtime-sumcheck -p runtime-zk`: 22 tests passed.
- ZK roundtrips cover both schedules, five layouts (including explicit Morton,
  lexicographic, output-major, reversed, and scrambled traversal), LFC1/LFC2,
  repeated nonadjacent input pairs, zero witnesses, and non-power-of-two width.
  Wrong-schedule verification and tampered proofs are rejected. Zero-width and
  zero-layer tests exercise both schedules.
- Core sumcheck proofs, auxiliary scalars, and transcripts are identical across
  term permutations for each fixed schedule when the initial transcript is
  held fixed. Full proofs retain the original order-sensitive circuit ID.
- The legacy RFC vector passes byte-for-byte in round-major mode.
- All four `mdoc-zk-runtime` release integration tests passed (73.10 seconds),
  including current v8 circuit-ID/positive/negative tests and historical
  compatibility tests. Historical v5-v7 specs select round-major; the current
  experimental v8 spec remains hand-major. This does not restore the old
  committed v8 circuit IDs previously replaced by the experiment.
- Workspace all-target checks and sumcheck/ZK all-target Clippy with warnings
  denied passed. Extending strict Clippy to mdoc hits an existing
  `byte_char_slices` warning in `mdoc_zk/proto/src/hash/constants.rs`.
- MLDSA-44 and MLDSA-65 stored-circuit and serialized-proof roundtrips passed
  under both schedules, period 6.

## MLDSA smoke benchmark

One release run per case, deterministic RNG seed 42, existing expanded-key /
supplied-mu fixtures. These are validation timings, not repeated-run medians.
Prove excludes commitment; verify includes receiving the commitment.
Peak memory was not remeasured.

| Circuit | Schedule | Commit ms | Prove ms | Verify ms | Proof bytes |
|---|---|---:|---:|---:|---:|
| MLDSA-44 | Hand-major | 251.320 | 898.155 | 681.742 | 665,736 |
| MLDSA-44 | Round-major | 255.004 | 1,513.362 | 677.452 | 665,896 |
| MLDSA-65 | Hand-major | 274.387 | 1,003.990 | 748.988 | 719,048 |
| MLDSA-65 | Round-major | 272.703 | 1,729.407 | 750.139 | 718,920 |

Proof geometry, witness count, and query count are unchanged. Transcript-dependent
Merkle multiproof paths can change serialized proof length; identical geometry
does not imply identical byte length.

| Circuit | Non-input wires | Terms | Layers | LFC1 bytes | LFC1 zstd16 | LFC2 bytes | LFC2 zstd16 |
|---|---:|---:|---:|---:|---:|---:|---:|
| MLDSA-44 | 3,449,557 | 6,580,787 | 37 | 78,996,522 | 669,700 | 2,670,639 | 997,383 |
| MLDSA-65 | 3,599,744 | 7,953,988 | 37 | 95,475,126 | 861,477 | 2,896,804 | 1,031,363 |

All circuit measurements and IDs are identical between schedules:

- MLDSA-44: `1c882777f206c0cf031a2a26ede3b17de2a5b1730ec3cf6d74a5cf62bff12e5f`
- MLDSA-65: `a7738549223e481d6651e22881c90bc0f6331d6b7cabb8f60afbff45bb76caa8`

Reproduce each schedule with:

```sh
MLDSA_SUMCHECK_ORDER=hand-major cargo test -p circuits-experimental --release --test experimental_tests proof_benchmark -- --ignored --nocapture --test-threads=1
MLDSA_SUMCHECK_ORDER=round-major cargo test -p circuits-experimental --release --test experimental_tests proof_benchmark -- --ignored --nocapture --test-threads=1
```

Raw logs for this run are `/tmp/mldsa-dual-order-hand-major.log` and
`/tmp/mldsa-dual-order-round-major.log`.
