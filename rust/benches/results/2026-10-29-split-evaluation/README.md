# Reuse one split circuit for witness evaluation and sumcheck

The prover builds all private SplitLayers before evaluating any layer. Witness evaluation traverses all eleven classes explicitly, using additions/subtractions for implicit unit coefficients and independent quadratic/linear assertion checks. It then moves the same split layers into sumcheck, releasing each layer after proving it. The Boolean prover uses the same ownership pattern. Conversion happens once per layer per proof, without hashes, token expansion, implementation macros or mutation of the source circuit.

The verifier continues splitting each layer once when deriving its public constraints. SplitLayer remains private to sumcheck v2. The ZK caller uses a combined evaluate_and_prove entry point and never sees the split representation. Standalone evaluation and supplied-witness proving entry points exist only under cfg(test).

The comparison baseline is fa577b6: three-stream witness evaluation followed by per-layer sumcheck splitting, with maximal buffer reservation. Both implementations use identical saved circuit artifacts, field arithmetic, commitment parameters and proof geometry. The compiler, proto, circuit definitions, IDs and serialized circuit files are unchanged. All eleven buffers still reserve their source's maximal stored-record capacity; retaining all split layers through witness evaluation can raise prover peak heap.

## End-to-end prover and verifier

Seven samples per implementation/application following a warmup; medians in milliseconds. Timers include circuit decoding, all split construction, witness evaluation, commitment/proof work, proof codecs and cleanup. NEXT also includes archive decompression. Offline circuit compilation, parameter selection and disk I/O are excluded.

| Circuit | fa577b6 P / V ms | Reused split P / V ms | Prover improvement | Proof bytes, both |
|---|---:|---:|---:|---:|
| next-2 | 165.508 / 87.562 | 163.023 / 84.741 | 1.5% | 185576 |
| next-4 | 180.300 / 92.402 | 171.879 / 89.845 | 4.7% | 187240 |
| mldsa-44 | 614.504 / 286.481 | 579.699 / 289.118 | 5.7% | 178964 |
| mldsa-65 | 711.408 / 333.148 | 674.589 / 338.741 | 5.2% | 188180 |

## Paired comparison with native eleven-stream circuits

A second run rotates the preserved native eleven-stream binaries against the new binaries under the same conditions. Each implementation reads its own matching circuit files: graph geometry and protocol rounds match, while circuit IDs and proof queries differ. All 56 proofs in this comparison verified. The native eleven-stream proof sizes are 184968, 187176, 178932 and 187380 bytes respectively; the current sizes are in the table above.

| Circuit | Native eleven-stream P / V ms | Reused split P / V ms | Prover delta ms | Verifier delta ms |
|---|---:|---:|---:|---:|
| next-2 | 157.355 / 85.315 | 162.548 / 84.117 | +5.192 | -1.199 |
| next-4 | 171.338 / 90.490 | 172.320 / 90.792 | +0.983 | +0.302 |
| mldsa-44 | 589.381 / 288.494 | 578.779 / 285.943 | -10.602 | -2.551 |
| mldsa-65 | 674.523 / 331.206 | 667.306 / 333.675 | -7.217 | +2.469 |

The large ML-DSA prover gap from generic witness evaluation is gone. NEXT-2 remains slower by about 5.2 ms, exceeding the isolated conversion cost. These end-to-end measurements do not identify the cause of that remaining gap. No phase attribution is claimed.

## Additional peak live heap

Separate allocation-tracking binaries; MiB = 2^20 bytes. These are requested live heap above each call's baseline, including reserved vector capacities, not RSS. Already resident serialized artifacts are excluded. Decoded circuit storage, the shared split representation and numerical work allocated during each call are included.

| Circuit | fa577b6 P / V MiB | Reused split P / V MiB |
|---|---:|---:|
| next-2 | 43.197 / 34.493 | 48.232 / 34.493 |
| next-4 | 48.001 / 37.592 | 53.063 / 37.592 |
| mldsa-44 | 101.440 / 38.312 | 132.168 / 38.312 |
| mldsa-65 | 106.420 / 43.664 | 139.763 / 43.664 |

## Unchanged circuit storage

Zstd level 16. NEXT raw and compressed sizes cover the complete signature/hash/manifest LFA2 bundle without its cache wrapper. Decoded heap below counts the original three-stream representation; private split storage is included in the operation peaks above.

| Circuit | Raw bytes | Zstd bytes | Decoded circuit heap bytes |
|---|---:|---:|---:|
| next-2 | 647225 | 173660 | 2248600 |
| next-4 | 672470 | 174989 | 2338580 |
| mldsa-44 | 1695926 | 505570 | 5209004 |
| mldsa-65 | 1879258 | 518948 | 5690584 |

## Validation and method

The full release suite with testonly, experimental and tooling enabled passed all 509 library tests, 27 tool tests and 2 doctests, with no skips, ignored tests or failures. All-target Clippy and compiler-, prover- and verifier-only checks passed. Frozen three-stream arithmetic independently verifies witness values, complete sumcheck proof bytes, constraints and transcript output over prime, binary and sextic fields. Existing tampering, Boolean-window, scalar/zero-layer and v1 compatibility tests pass. Serializing circuits before and after evaluation/proving/reduction confirms that their original representation and IDs remain unchanged.

AMD Ryzen 9 9950X, Rust 1.99.1, native release build with LTO, CPU boost disabled, one thread pinned to CPU 2. Eight application/implementation cases rotate and reverse order across seven repetitions following one warmup each. Builds, tests and preparation are idle during timing. Every one of the 56 measured proofs verified; every ML-DSA iteration rejected a changed public key outside its successful verification timer. Proof sizes match between implementations. ML-DSA uses the existing prime-field circuit.

## Reproduction and data

[run.rs](run.rs) stages benchmark executables and uses /tmp/split-evaluation-benchmark. Baseline timing/memory binaries come from fa577b6 and are preserved in baseline/timing and baseline/memory. Both implementations read identical copies of the saved circuits. Build timing executables with cargo build --release --bench mdoc_zk_bench_next --bench mldsa_bench_v2 --features testonly,experimental, then run stage-time. Rebuild with bench-memory and run stage-memory. Run memory separately, then time once all builds/checks are idle.

The driver reads baseline artifacts from baseline/circuits and current artifacts from circuits. For the native eleven-stream comparison, use /tmp/split-evaluation-eleven with the preserved eleven-stream binaries and artifacts under baseline, and the current timing binaries and three-stream artifacts at the root; run eleven-time. This comparison deliberately permits different proof sizes because its circuit IDs differ. Smoke checks use smoke and eleven-smoke.

Data: [samples](samples.csv), [medians](medians.csv), [native eleven-stream samples](eleven-samples.csv), [native eleven-stream medians](eleven-medians.csv), [peak heap](memory.csv), [circuit sizes](sizes.csv), [geometry](geometry.csv), [term breakdown](terms.csv), [executable checksums](binaries.sha256). The [preceding report](../2026-10-29-layer-split/README.md) compares native three-stream, counted and maximal split buffers. The [original native eleven-stream report](../2026-10-29-next-v9/README.md) records its format and circuit storage.
