# ML-DSA validation after HEAD restoration and cleanup

Date: 2026-09-11. Production baseline: `fa578cc5bb055d72df379dc195393ea2f124788e`.

Both retained variants pass end-to-end proof generation and verification against
the first committed C++ vector for each parameter set. The stored segmented LFC2
circuit is decoded with circuit-ID checking; the proof is serialized, decoded
using verifier-derived geometry, checked for equality and full byte consumption,
and the decoded proof is verified. All six final runs passed.

## Scope and configuration

- Production compiler, scheduler, mdoc code, runtime, and all C++ source match HEAD.
  All remaining source changes are confined to the experimental Rust ML-DSA crate.
- Period 6 and XOR-basis SHAKE are retained. No optional wire renaming, lane-order,
  or template-roundtrip policy is enabled. Stock global Morton ordering and LFC2
  segmentation are used; the existing prover consumes the decoded LFC2 circuit.
- These are signature-on-mu circuits with an expanded public key. Key expansion
  and message-to-mu hashing happen natively, outside the circuit. The benchmark
  makes the expanded key public and mu private. It does not establish an
  application-level binding to a public message.
- Runtime field: Fp24 degree-six extension; base-subfield encoding: 4 bytes;
  CRT Reed-Solomon interpolation; Ligero rate inverse 4, 128 queries.
- AMD Ryzen 9 9950X; rustc 1.97.1; release opt-level 3, LTO, one codegen unit.
  Three sequential fresh-process runs per variant, alternating 44 and 65,
  with no concurrent builds or test suites in the final timing batch.
- Timings exclude compilation, witness construction, circuit encoding/decoding,
  compression, proof serialization/deserialization, and verifier geometry setup.
  Prover total is commit plus prove, computed per run before taking the median.
  Verify includes commitment receipt and verification. The test's printed total
  includes all setup and compression and is not the prover time.

## Median times

| Operation | ML-DSA-44 (s) | ML-DSA-65 (s) |
|---|---:|---:|
| Commit | 0.248565 | 0.273643 |
| Prove excluding commit | 1.083117 | 1.145966 |
| Prover total | 1.330795 | 1.421975 |
| Verify | 0.701294 | 0.751328 |

## Circuit geometry

| Metric | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|
| Input wires (including constant 1) | 128,272 | 156,263 |
| Public input wires (including constant 1) | 5,121 | 9,217 |
| Non-input wires (compiler nwires) | 3,449,557 | 3,599,744 |
| Terms | 6,580,787 | 7,953,988 |
| Layers | 37 | 37 |
| Output wires | 2,263 | 2,336 |
| Assertions | 144,961 | 172,323 |
| Proof witnesses including ZK padding | 125,766 | 149,677 |
| Proof constraints | 37 | 37 |
| Ligero block_enc | 5,699 | 6,113 |

## Serialized sizes (exact bytes)

| Metric | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|
| ZK proof | 665,608 | 718,216 |
| LFC1 | 78,996,522 | 95,475,126 |
| LFC1 + zstd-16 | 2,987,771 | 3,060,896 |
| LFC1 + zstd-22 | 2,933,070 | 2,917,836 |
| Segmented LFC2 | 7,275,471 | 7,361,859 |
| Segmented LFC2 + zstd-16 | 3,857,534 | 3,877,321 |
| Segmented LFC2 + zstd-22 | 3,776,435 | 3,800,283 |

Sizes and geometry are identical across all three final runs for each variant,
and match the pre-cleanup measurements against the restored scheduler. This
cleanup does not implement a size optimization: neither variant meets the earlier
500,000-byte compressed-circuit target. LFC1 compresses smaller than segmented
LFC2 in this baseline, despite being much larger before compression.

Compression uses zstd 1.5.7 through Rust zstd 0.13.3. Byte counts are the complete
outputs of the existing circuit/proof serializers, not just term payloads.
Proof bytes do not include the circuit or public inputs.

## Individual final timing runs

| Variant | Run | Commit (s) | Prove (s) | Prover total (s) | Verify (s) |
|---|---:|---:|---:|---:|---:|
| ML-DSA-44 | 1 | 0.249168 | 1.085022 | 1.334191 | 0.700306 |
| ML-DSA-44 | 2 | 0.247678 | 1.083117 | 1.330795 | 0.703068 |
| ML-DSA-44 | 3 | 0.248565 | 1.079021 | 1.327586 | 0.701294 |
| ML-DSA-65 | 1 | 0.272065 | 1.154105 | 1.426171 | 0.751328 |
| ML-DSA-65 | 2 | 0.273643 | 1.140060 | 1.413703 | 0.748780 |
| ML-DSA-65 | 3 | 0.276009 | 1.145966 | 1.421975 | 0.754346 |

Raw logs: `results/head-cleanup-{44,65}-{1,2,3}.log`.

## Cleanup and checks

- Shared the committed C++ fixture parser, added whole-byte hex validation and
  parser tests, and removed duplicate parser implementations.
- Shared circuit construction across analysis, evaluation, and proof tests.
- Removed shadowed names in library SHAKE code and the benchmark's circuit stages;
  simplified redundant offline-helper conditions; applied rustfmt.
- Documented the supplied-mu / expanded-key circuit boundary and benchmark scope.
- Added proof serialization round-trip checks and comparison with the C++ mu.
- Retained all experimental analysis support under `experiments/mldsa`, with
  documentation distinguishing historical results from this restored baseline.
- Fixed the standalone `mldsa-runtime` feature's dependency on bitvec witness
  helpers without changing the committed bitvec crate.

Validation passed:

```sh
cargo check -p circuits-experimental --no-default-features --lib
cargo check -p circuits-experimental --no-default-features --features mldsa-runtime --lib
cargo clippy -p circuits-experimental --all-features --lib --no-deps -- -D warnings
cargo fmt -p circuits-experimental -- --check
cargo test -p circuits-experimental --all-features --all-targets
cargo test --release -p circuits-experimental --all-features
```

Ordinary tests: 48 passed, 6 explicitly ignored, in both development and release
profiles. The two ignored proof benchmarks were then run separately three times
each and passed. The remaining ignored tests are offline analysis, field timing,
and the two evaluation-only full-circuit tests. Native malformed-signature tests
and in-circuit norm/hint boundary rejection tests are part of the ordinary suite.
This is correctness/regression validation, not a full cryptographic soundness audit.
The warning-denied Clippy check covers the library; older offline analysis helpers
still have shadow-variable style warnings in the all-targets Clippy check.

Reproduce the end-to-end runs from the Rust workspace root:

```sh
env -u MLDSA_WIRE_POLICY -u MLDSA_LANE_ORDER -u MLDSA_TEMPLATE_ROUNDTRIP cargo test --release -p circuits-experimental --all-features mldsa44_proof_benchmark -- --ignored --nocapture
env -u MLDSA_WIRE_POLICY -u MLDSA_LANE_ORDER -u MLDSA_TEMPLATE_ROUNDTRIP cargo test --release -p circuits-experimental --all-features mldsa65_proof_benchmark -- --ignored --nocapture
```

Rollback recovery files are in `/tmp/longfellow-nonmldsa-revert.K07Rgp`: the prior
non-MLDSA diff, the removed sumcheck test, and two removed C++ benchmark helpers.
