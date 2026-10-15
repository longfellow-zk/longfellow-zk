# Release C++ versus selected Rust MLDSA

## Configuration and scope

Both MLDSA-44 and MLDSA-65 use period 4, an extra cut after round 0, no bit pluckers, and `subfield_boundary = ninput`. Cuts are after zero-based rounds [0,3,7,11,15,19,23]. Both prove the first committed C++ fixture, with an expanded public key and a supplied private mu. Key expansion and message-to-mu hashing are outside these circuits. Both use the same fp24 degree-six extension (q=8,380,417, x^6−7), XOR-basis SHAKE operations, CRT-based Reed–Solomon interpolation, Ligero rate inverse 4, and 128 opened columns.

The only C++ configuration changes are the requested slicing overlay and full-input subfield metadata. The harness includes the committed C++ test source. The C++ source tree under lib/ is unchanged; the isolated include overlay is used by both circuit and witness templates. Native SHAKE witness construction records all 24 rounds and is unaffected in the reused object code. All original input witnesses were checked to lie in the subfield.

| Remaining difference | Rust | C++ |
|---|---|---|
| Sumcheck | Dense hand-major | Existing round-major / sparse binding |
| Circuit order | Whole / shape_classes / reuse | Existing Morton ordering |
| Main stored format | Segmented LFC2 | LFC1 |
| Field serialization | 18-byte extension / 3-byte base | 24-byte extension / 4-byte base |
| Ligero block selection | Existing CRT-aware optimizer | Existing power-of-two optimizer |
| Release compilation | rustc 1.97.1, O3/LTO, native CPU | GCC 14.2.0, O3, NDEBUG, mpclmul; existing CMake optimization settings |
| Benchmark RNG | Existing deterministic test RNG | Existing SecureRandomEngine |

Hardware: AMD Ryzen 9 9950X. All four timing batches ran serially, with no compilation or compression overlap; five complete verified flows per implementation/variant. Prover time is commit + prove; setup, loading, witness generation and serialization are excluded. Verification includes commitment receipt and verification of the parsed proof, but excludes proof parsing and verifier construction. Each proof was serialized, parsed, and verified. Rust additionally asserted byte equality with the previously saved selected proof.

Peak RSS is measured with `/usr/bin/time -v` in a separate fresh one-flow process per implementation/variant. It includes circuit loading, native witnesses, proving, proof parsing, and verification; it excludes offline circuit compilation and compression. C++ loads its raw LFC1 file; Rust loads raw LFC2. Loading is part of memory use, not prover time. The timing-process multi-flow high-water marks are not used as the headline memory measurement.

These are implementation/configuration comparisons, not a controlled claim about the intrinsic speed of C++ versus Rust. Serialization, scheduling, geometry selection, and compiler settings still differ as requested.

## Circuit geometry

| Metric | Rust 44 | C++ 44 | Rust 65 | C++ 65 |
|---|---:|---:|---:|---:|
| Input wires | 166,672 | 167,184 | 194,663 | 195,175 |
| Public input wires | 5,121 | 5,633 | 9,217 | 9,729 |
| Private input wires | 161,551 | 161,551 | 185,446 | 185,446 |
| Output wires | 2,920 | 3,000 | 2,920 | 3,000 |
| Total wires, including inputs/outputs | 3,613,574 | 3,497,062 | 3,791,554 | 3,685,656 |
| Non-input wires | 3,446,902 | 3,329,878 | 3,596,891 | 3,490,481 |
| Terms | 6,691,580 | 6,993,968 | 8,064,583 | 8,344,031 |
| Layers | 24 | 25 | 24 | 25 |
| Maximum layer/input width | 413,882 | 421,644 | 457,559 | 467,008 |
| Sum of layer-local distinct deltas | 49,849 | 296,899 | 51,169 | 331,898 |
| Distinct coefficients | 1,112 | 1,077 | 1,120 | 1,075 |
| Proof witnesses, including padding | 163,303 | 163,374 | 187,198 | 187,269 |
| Padding witnesses | 1,752 | 1,823 | 1,752 | 1,823 |
| Proof constraints | 24 | 25 | 24 | 25 |
| Ligero block_enc | 6,125 | 8,192 | 6,143 | 8,192 |

C++ retains 64 public bytes (512 input wires) for `Pk::tr`; `assert_valid_signature_on_mu` does not consume them. Rust omits that unused field. Private input counts therefore match exactly. This difference was not changed in C++, per the instruction to leave everything else alone. Total wires use the same convention on both sides: final output width plus the sum of each layer input width.

## Bytes

| Metric | Rust 44 | C++ 44 | Rust 65 | C++ 65 |
|---|---:|---:|---:|---:|
| Raw LFC1 | 80,319,249 | 83,953,746 | 96,795,429 | 100,154,454 |
| LFC1 zstd-22 | 323,094 | 815,935 | 328,698 | 812,569 |
| Raw LFC2 | 1,642,397 | — | 1,805,553 | — |
| LFC2 zstd-22 | 367,947 | — | 377,432 | — |
| Proof, median | 218,708 | 294,512 | 227,852 | 304,592 |
| Proof, minimum | 218,708 | 294,160 | 227,852 | 303,952 |
| Proof, maximum | 218,708 | 294,864 | 227,852 | 304,720 |

All sizes are exact bytes. C++ has no LFC2 implementation, so those entries are intentionally blank. Both compression paths use zstd 1.5.7 at level 22. Rust LFC1 is smaller after compression than LFC2, but LFC2 is the selected directly usable compact runtime representation. The experimental relative-reference LFR1 format is not used in these benchmarks. C++ proof byte counts vary across samples because its RNG is nondeterministic and Merkle paths are batched. Circuit and public-input bytes are not included in proof size.

## Performance

| Metric | Rust 44 | C++ 44 | Rust 65 | C++ 65 |
|---|---:|---:|---:|---:|
| Commit, ms | 300.556 | 308.274 | 343.899 | 351.783 |
| Prove excluding commit, ms | 865.881 | 2,542.809 | 1,003.744 | 2,760.896 |
| Total prover, ms | 1,168.284 | 2,853.072 | 1,358.517 | 3,112.679 |
| Verifier, ms | 720.759 | 1,559.749 | 819.540 | 1,712.834 |
| Load + ID, ms | 158.929 | 428.047 | 190.690 | 520.831 |
| Fresh-process peak RSS, MiB | 126.7 | 190.1 | 136.2 | 208.2 |

Load+ID is diagnostic: C++ loads once per five-flow process while Rust reloads before each flow. It includes file reading and ID validation, not zstd decompression. No isolated FFT/CRT microbenchmark was rerun; the table measures complete end-to-end proof arithmetic.

## Interpretation

- MLDSA-44: Rust has 4.32% fewer terms and 3.33% more wires. Its selected compressed LFC2 is 54.90% smaller than C++ compressed LFC1. Proving is 2.44× faster, verification 2.16× faster; proofs are 25.74% smaller and peak RSS 33.36% lower.
- MLDSA-65: Rust has 3.35% fewer terms and 2.87% more wires. Its selected compressed LFC2 is 53.55% smaller than C++ compressed LFC1. Proving is 2.29× faster, verification 2.09× faster; proofs are 25.19% smaller and peak RSS 34.57% lower.

The earlier 2.3× term regression is not present in this aligned comparison. The remaining compressed-size gap is much larger than the small term-count difference: Rust has far fewer distinct coordinate deltas and a different traversal/storage policy. Proof-size savings should not all be attributed to scheduling: the 18/3 versus 24/4 byte encoding and different block selection are substantial confounders. No additional C++ optimization was applied.

## Artifacts

[C++ harness](cpp_compare.cc) · [Slicing overlay](cpp_compare_include/circuits/tests/sha3/sha3_slicing.h) · [Summary CSV](results/cpp-aligned-summary.csv) · [Individual timing samples](results/cpp-aligned-timings.csv)

Raw circuits, compressed C++ circuits, serialized C++ proofs, geometry logs, timing logs and fresh-memory logs are under `target/cpp-aligned`. C++ compilation/compression ran separately and in parallel; the compile times and compiler peak RSS in those logs are diagnostics, not comparable prover measurements.
