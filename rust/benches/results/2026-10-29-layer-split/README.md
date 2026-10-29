# Private per-layer sumcheck split

Measurements for fa577b6, before split witness evaluation. The
[current report](../2026-10-29-split-evaluation/README.md) reuses one split circuit
for both evaluation and sumcheck.

Sumcheck v2 builds a private SplitLayer at the beginning of each prover or reduction layer, reuses it for that layer's bindings and affine corrections, and drops it before the next layer. Original LFC3 circuits remain three-stream and read-only. This runtime optimization preserves compiler behavior, the stored format, circuit IDs, archive bytes and parameters.

SplitLayer is declared pub(super) inside the private sumcheck_v2::split module. It is not re-exported or used outside sumcheck v2. Its constructor takes &Layer and no field or coefficient values. Only coefficient indices are classified: 0 for assertions, 1 for one, 2 for minus one, all others general. Quadratic and linear terms each produce four streams; constants produce three, since zero constant records are invalid.

Stored source segments are split once, retaining their segment IDs. Each class reserves a contiguous record buffer large enough for all records in its source segment definitions. A single emission pass appends adjusted records directly; no coefficient-counting pass is needed. A range table maps each original segment ID into that class's buffer. Original token slices are borrowed. A single coordinate-advance table per source stream retains each segment's full displacement; skipped classes and empty segments still advance correctly. There are no hashes, deduplication tables, dictionary rebuilding, per-segment record-vector allocations, repeated-token expansion, or token rewriting. Original source dictionaries are read only. No Arc, Box, Option or persistent split cache is needed.

Numerical bindings traverse all eleven classes separately over contiguous segment ranges, without a second delta-index lookup. Unit and negative streams avoid coefficient multiplications; assertions retain independent transcript coefficients. Generic coefficient loops contain no special-value branch. The optional Boolean kernel also receives SplitLayer. Witness evaluation continues reading the original three-stream circuit.

## Prover / verifier medians

Seven timed samples per implementation/application following a warmup. Entries are milliseconds. The split columns include per-layer construction and cleanup. Counted split reserves exact class capacities after a counting pass; maximal split reserves the full stored source length for each class and emits once.

| Circuit | Native three-stream P / V | Counted split P / V | Maximal split P / V | Proof bytes, all |
|---|---:|---:|---:|---:|
| next-2 | 179.357 / 95.578 | 165.825 / 87.783 | 166.951 / 87.672 | 185576 |
| next-4 | 194.812 / 100.871 | 180.457 / 92.827 | 180.051 / 92.926 | 187240 |
| mldsa-44 | 692.787 / 328.622 | 622.019 / 288.632 | 621.007 / 290.317 | 178964 |
| mldsa-65 | 788.702 / 376.378 | 714.595 / 332.675 | 716.505 / 339.446 | 188180 |

## Peak additional live heap

Separate executables enable allocation tracking; timing executables disable it. MiB = 2^20 bytes. These are requested live heap above each call's baseline, including reserved vector capacity, not RSS. Serialized circuit bytes/fixtures already resident before the call are excluded; decoding, split construction and numerical work during the call are included. Unused capacity in the maximal buffers is not initialized.

| Circuit | Native three-stream P / V MiB | Counted split P / V MiB | Maximal split P / V MiB |
|---|---:|---:|---:|
| next-2 | 42.646 / 34.280 | 42.770 / 34.334 | 43.197 / 34.493 |
| next-4 | 47.502 / 37.359 | 47.626 / 37.418 | 48.001 / 37.592 |
| mldsa-44 | 101.341 / 36.594 | 101.371 / 36.934 | 101.440 / 38.312 |
| mldsa-65 | 106.321 / 40.815 | 106.352 / 41.129 | 106.420 / 43.664 |

## Isolated split construction

A separate warm diagnostic constructs and drops each layer individually from already decoded circuits, with three warmups and 31 samples pinned to CPU 2. Values below sum per-layer timings; constructor and destructor medians are reported separately. NEXT signature and hash components are measured separately. These timers exclude decoding, witness evaluation and numerical sumcheck.

| Component | Stored segment records | Counted build / drop ms | Maximal build / drop ms |
|---|---:|---:|---:|
| next-2-signature | 107814 | 0.322 / 0.002 | 0.228 / 0.003 |
| next-2-hash | 148566 | 0.413 / 0.002 | 0.308 / 0.003 |
| next-4-signature | 107814 | 0.323 / 0.002 | 0.226 / 0.003 |
| next-4-hash | 153441 | 0.429 / 0.002 | 0.319 / 0.003 |
| mldsa-44 | 709983 | 2.228 / 0.005 | 2.050 / 0.088 |
| mldsa-65 | 764225 | 2.325 / 0.005 | 2.273 / 0.106 |

## Unchanged circuit storage

The same saved circuit files are used by all three implementations. Zstd level 16; NEXT sizes cover the complete signature/hash/manifest LFA2 bundle, excluding its local cache wrapper. Decoded heap counts the original three-stream representation; temporary per-layer working storage is captured by the peak measurements above.

| Circuit | Raw bytes | Zstd bytes | Decoded circuit heap bytes |
|---|---:|---:|---:|
| next-2 | 647225 | 173660 | 2248600 |
| next-4 | 672470 | 174989 | 2338580 |
| mldsa-44 | 1695926 | 505570 | 5209004 |
| mldsa-65 | 1879258 | 518948 | 5690584 |

## Validation and method

The complete release suite with testonly, experimental and tooling enabled passed 509 library tests, 27 tool tests and 2 doctests, with no exclusions, ignored tests or failures. The new regression tests verify segment boundaries, empty and repeated segments, wrapping coordinate deltas, preserved class-relative term/assertion order, and borrowed token identity. Randomized bindings match the frozen three-stream reference over prime, binary and sextic fields. Complete sumcheck proof bytes, constraints and transcript output also match that reference, and serializing the original circuit before and after proving/reduction produces identical bytes.

The runtime split preserves the three-stream format, compiler behavior and circuit identity. Final cleanup expands the v2 traversal, codec, identity and compression helper macros into explicit Rust without changing those semantics. Original saved circuit artifacts retain their checksums. Source references to SplitLayer are confined to sumcheck-v2. Compiler-, prover- and verifier-only builds plus all-target experimental Clippy checks passed. V1 compatibility tests remain unchanged and pass.

The paired benchmark uses the preserved native-three-stream timing and memory binaries as baseline and the new split binaries against copies of exactly the same artifacts. AMD Ryzen 9 9950X, Rust 1.99.1, native release build with LTO, boost disabled, one thread pinned to CPU 2. Twelve cases rotate and reverse order across seven repetitions, after one warmup each. Builds, tests and preparation are idle during timing. Every one of the 84 measured proofs verified; each ML-DSA iteration also rejected a changed public key outside its successful verification timer. Proof sizes match for all three implementations.

Times include circuit decoding, witness/public-input preparation, commitment, proof codecs, numerical operations and cleanup. NEXT also includes archive decompression. ML-DSA uses native prime-field arithmetic and memory-resident raw circuits. Offline compilation, disk I/O and parameter selection are excluded. Split work occurs inside each online prover/verifier timer, not during circuit loading or preparation.

## Reproduction and data

[run.rs](run.rs) stages the newest mdoc_zk_bench_next and mldsa_bench_v2 executables and uses /tmp/layer-split-benchmark for binaries, caches and logs. Baseline timing/memory executables are copied from /tmp/native-three-benchmark into baseline/timing and baseline/memory. Preserve the counted-split timing/memory binaries in counted/timing and counted/memory before staging the maximal-split binaries. Saved circuit artifacts are copied into circuits; the original source files are untouched. Build the new timing family with --release --features testonly,experimental, then run stage-time. Rebuild with bench-memory and run stage-memory. Run memory separately, then time after all builds/checks finish.

The native-three-stream report provides the exact baseline implementation and artifact generation commands. This benchmark does not introduce a runtime selector or format variant. The three implementations are separate binaries; the production path always splits each layer once.

Data: [counted constructor](split-counted.csv), [maximal constructor](split-maximal.csv), [samples](samples.csv), [medians](medians.csv), [peak heap](memory.csv), [sizes](sizes.csv), [geometry](geometry.csv), [term breakdown/dictionaries](terms.csv). Baseline: [native three-stream LFC3](../2026-10-29-native-three/README.md).
