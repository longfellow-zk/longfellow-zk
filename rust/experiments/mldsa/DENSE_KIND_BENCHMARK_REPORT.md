# Integrated ML-DSA: dense sumcheck and type/output-major LFC2

Recorded 2026-09-11 on the `rust` working tree, based on production commit
`fa578cc5bb055d72df379dc195393ea2f124788e`. ML-DSA sources/support were imported
from `mldsa` commit `e8794c51f6862e47fbd7224b22631a9958d1b45f`.
No commit was created by this integration.

## Result

Both ML-DSA-44 and ML-DSA-65 work with the same compiler ordering and dense prover
already used by mdoc. No production scheduler/prover change was needed during
integration. All six uninstrumented timing runs and both separately instrumented
memory runs produced serialized proofs that decoded and verified successfully.

The type/output-major traversal reduces zstd-16 segmented LFC2 size by **74.1%**
for ML-DSA-44 and **73.4%** for ML-DSA-65 against the recorded branch baseline.
Neither reaches the 500,000-byte target. LFC1 compresses smaller than LFC2 for
these circuits; the remaining size problem is not solved by this integration.

## Cryptographic times

Seconds, medians of three fresh-process measurements per variant. Prover total
is commit + prove, computed for each run before taking its median.

| Operation | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|
| Commit | 0.247515 | 0.272031 |
| Prove excluding commit | 0.872575 | 0.982960 |
| Prover total | 1.120090 | 1.256153 |
| Verify | 0.672281 | 0.751028 |

Compared with the [recorded restored-HEAD branch baseline](HEAD_VALIDATION_REPORT.md):

| Metric | ML-DSA-44 baseline → current | ML-DSA-65 baseline → current |
|---|---:|---:|
| Prover total (s) | 1.330795 → 1.120090 | 1.421975 → 1.256153 |
| Verify (s) | 0.701294 → 0.672281 | 0.751328 → 0.751028 |
| LFC2 + zstd-16 (B) | 3,857,534 → 997,383 | 3,877,321 → 1,031,363 |

Prover total improves 15.8% / 11.7%. Verification improves 4.1% for ML-DSA-44 and
is essentially unchanged for ML-DSA-65. Baseline comparisons use saved earlier
runs on the same machine, not a freshly interleaved A/B experiment.

## Peak memory

One separate allocation-tracked run per variant; timing results above exclude
these runs. Values below are bytes of **additional live heap above operation
entry**, not absolute resident memory and not net retained allocations.

| Phase | ML-DSA-44 B | ML-DSA-65 B |
|---|---:|---:|
| Commit | 28,389,684 | 33,332,436 |
| Prove excluding commit | 90,284,524 | 94,810,948 |
| Prover total (commit + prove) | 112,464,132 | 120,797,940 |
| Verify | 22,056,184 | 25,316,376 |

Prover total peaks are **107.254 / 115.202 MiB**;
verifier peaks are **21.034 / 24.144 MiB**.

The total prover heap peak includes the commitment retained between phases:
max(commit absolute peak, prove absolute peak) minus live heap before commit.
It is not the sum or maximum of the two phase-relative peaks. Circuit decoding,
input construction, proof serialization/deserialization and verifier geometry
construction are outside these measured operation regions.

Maximum whole-process RSS across all four runs per variant:
**1,808,988 KiB / 2,572,272 KiB**
(1.725 / 2.453 GiB).
This includes compiler/setup/compression allocations. The executable was launched
directly under `/usr/bin/time -v`, so Cargo/rustc memory is excluded.
Untracked timing-run RSS maxima were 1,806,340 /
2,559,488 KiB. No comparable per-operation heap
measurement was recorded in the old branch baseline.

## Circuit and proof sizes

Complete serialized files, exact bytes. Geometry and sizes matched in all four
runs per variant, including the instrumented runs.

| Format | ML-DSA-44 B | ML-DSA-65 B |
|---|---:|---:|
| LFC1 | 78,996,522 | 95,475,126 |
| LFC1 + zstd-16 | 669,700 | 861,477 |
| LFC1 + zstd-22 | 616,173 | 640,820 |
| Segmented LFC2 | 2,670,639 | 2,896,804 |
| Segmented LFC2 + zstd-16 | 997,383 | 1,031,363 |
| Segmented LFC2 + zstd-22 | 959,815 | 989,616 |
| ZK proof | 665,736 | 719,048 |

Proofs exclude the circuit and public inputs. Fixed proof geometry is unchanged.
The measured proof sizes are 128 / 832 bytes larger than the recorded baseline;
changed circuit IDs and hand scheduling change Fiat–Shamir challenges and the
variable-length Merkle multiproof paths. No extra witnesses were introduced.

## Geometry and configuration

| Metric | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|
| Inputs including reserved One | 128,272 | 156,263 |
| Public inputs including One | 5,121 | 9,217 |
| Non-input wires | 3,449,557 | 3,599,744 |
| Terms | 6,580,787 | 7,953,988 |
| Layers | 37 | 37 |
| Outputs | 2,263 | 2,336 |
| Assertions | 144,961 | 172,323 |
| Proof witnesses including padding | 125,766 | 149,677 |
| Proof constraints | 37 | 37 |
| Ligero block_enc | 5,699 | 6,113 |
| Sum of per-layer delta dictionary entries | 178,492 | 176,295 |
| Sum of per-layer segment dictionary entries | 30,026 | 32,879 |

Geometry matches the branch baseline exactly. Period 6 and XOR-basis SHAKE are
retained. Field: Fp24 degree-six extension, four-byte base-subfield encoding,
unchanged CRT Reed–Solomon interpolation. Ligero rate inverse 4, 128 queries.

The benchmarks use the first committed C++ vector for each parameter set.
They verify signatures on a **supplied mu with an expanded public key**:
key expansion and message-to-mu hashing are native witness preparation, outside
the circuit. The expanded key is public; mu and the signature are private.
This is not a complete application circuit binding a public message.

Current IDs:

- ML-DSA-44: `1c882777f206c0cf031a2a26ede3b17de2a5b1730ec3cf6d74a5cf62bff12e5f`
- ML-DSA-65: `a7738549223e481d6651e22881c90bc0f6331d6b7cabb8f60afbff45bb76caa8`

## Validation

- Release experimental suite: 48 passed, six explicitly ignored.
- The two ignored proof benchmarks were then run separately four times each:
  six timing runs + two allocation-tracked runs, all passed.
- Every benchmark decodes the stored segmented LFC2 with ID checking, serializes
  the proof, decodes it using verifier-derived geometry, checks equality/full byte
  consumption, and verifies the decoded proof.
- Native malformed-signature and in-circuit norm/hint boundary tests passed as
  part of the ordinary suite.
- Standalone library checks passed with no default features and with mldsa-runtime.
- Library Clippy passed with `--all-features --no-deps -- -D warnings`.
- Experimental crate formatting check and `git diff --check` passed.
- Full mdoc v8 regression suite passed for 1–4 attributes with unchanged current
  circuit IDs. No C++ source or existing dense runtime source changed in this turn.

Historical Morton/template analysis helpers and logs were preserved. Those
opt-in helpers may require Morton-ordered control inputs; they are not enabled
in the default proof path.

## Individual uninstrumented runs

| Variant | Run | Commit s | Prove s | Prover total s | Verify s | RSS KiB |
|---|---:|---:|---:|---:|---:|---:|
| 44 | 1 | 0.247515 | 0.872575 | 1.120090 | 0.669515 | 1,806,180 |
| 44 | 2 | 0.248953 | 0.873260 | 1.122213 | 0.673154 | 1,806,324 |
| 44 | 3 | 0.247212 | 0.870103 | 1.117315 | 0.672281 | 1,806,340 |
| 65 | 1 | 0.271476 | 0.993078 | 1.264554 | 0.761328 | 2,559,232 |
| 65 | 2 | 0.273193 | 0.982960 | 1.256153 | 0.751028 | 2,559,232 |
| 65 | 3 | 0.272031 | 0.977803 | 1.249833 | 0.745101 | 2,559,488 |

## Reproduction

AMD Ryzen 9 9950X, rustc 1.97.1, Linux x86-64. Release opt-level 3, LTO, one codegen
unit. Three sequential fresh processes per variant, alternating 44 and 65,
without concurrent builds/tests. Native setup, circuit compilation, circuit
encoding/decoding/compression, proof serialization/deserialization, and verifier
geometry setup are excluded from crypto times. Verify includes commitment receipt.
The printed benchmark `total` is the entire test, not prover time.

```sh
cargo test --release -p circuits-experimental --features testonly --no-run
cargo test --release -p circuits-experimental --all-features --no-run
```

The first builds the uninstrumented timing executable; the second enables the
test-only `bench-memory` allocator. Use the executable paths emitted by Cargo.
For these builds, timing was `experimental_tests-3270441737c18afa` and tracked
memory was `experimental_tests-659d6e593f10c952`, both under `target/release/deps/`.

Invoke each executable directly, substituting 44 or 65:

```sh
env -u MLDSA_WIRE_POLICY -u MLDSA_LANE_ORDER -u MLDSA_TEMPLATE_ROUNDTRIP \
  /usr/bin/time -v -o /tmp/mldsa-44-rss.log \
  target/release/deps/experimental_tests-3270441737c18afa \
  --exact all::mldsa_verifier::mldsa44_proof_benchmark \
  --ignored --nocapture --test-threads=1
```

Use the tracked executable for memory and leave timing measurements from that
run out of the timing aggregate. Heap counters require isolated tests.

Raw logs: `results/dense-kind-{44,65}-{1,2,3,memory}.log`, with corresponding
`-rss.log` files. Machine-readable results and recorded-baseline comparisons:
[results/dense-kind-summary.json](results/dense-kind-summary.json).
