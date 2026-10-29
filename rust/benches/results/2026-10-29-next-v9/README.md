# NEXT v9 and ML-DSA: LFC3 benchmark

NEXT is v9, using the single default compiler configuration. Both applications use compile_v2, the native v2 circuit representation, and LFC3's eleven streams. NEXT uses an LFA2 archive containing signature, hash and input-manifest entries; ML-DSA is measured as an individual LFC3 circuit. Neither path reserves a One wire. V8 and alternative v9 configurations are unsupported.

## Circuit storage and resident allocations

Zstd level 16. NEXT sizes exclude the offline cache wrapper. Decoded heap counts owned allocation capacities, including macro dictionaries and layer records.

| Circuit | Raw bytes | Zstd bytes | Decoded heap bytes |
|---|---:|---:|---:|
| next-2 | 575951 | 157378 | 2046716 |
| next-4 | 594943 | 158323 | 2123444 |
| mldsa-44 | 1679298 | 515043 | 5199000 |
| mldsa-65 | 1869518 | 535961 | 5715720 |

## Online proof operations

Median of seven timed samples following one warmup per circuit, one thread pinned to CPU 2. Cases rotate and reverse order between samples. AMD Ryzen 9 9950X, Rust 1.99.1, native release build, CPU boost disabled. Timing runs have allocation tracking disabled and run separately from heap instrumentation. Every timed proof verified.

Times include circuit decoding, witness preparation, commitment, proving/verifying, proof codecs and cleanup. NEXT includes zstd circuit decompression. ML-DSA loads raw circuits and rejects a modified public key outside the successful-operation timers. Preparation and offline parameter selection are excluded.

| Circuit | Prover ms | Verifier ms | Proof bytes | Prover peak MiB | Verifier peak MiB |
|---|---:|---:|---:|---:|---:|
| next-2 | 158.545 | 85.475 | 184968 | 42.454 | 34.087 |
| next-4 | 171.228 | 90.710 | 187176 | 47.297 | 37.154 |
| mldsa-44 | 577.633 | 290.148 | 178932 | 101.331 | 36.584 |
| mldsa-65 | 671.325 | 328.372 | 187380 | 106.345 | 40.839 |

Peak heap is the additional live requested allocation during each operation, measured separately with bench-memory; it is not RSS. Serialized circuit bytes and fixtures already resident before the call are excluded; circuit decoding allocations made during the call are included. Exact byte counts are in [memory.csv](memory.csv).

## Expanded terms by class

Assertions are sampled separately from ordinary terms. The two NEXT attribute counts share the signature circuit. All counts below describe expanded logical occurrences; dictionaries remain compressed in memory. Dictionary-record, segment and token counts are also recorded in [terms.csv](terms.csv).

| Circuit / component | Term type | Assertions | +1 | -1 | General |
|---|---|---:|---:|---:|---:|
| next-2 / signature | quadratic | 0 | 66770 | 6950 | 68118 |
| next-2 / signature | linear | 3958 | 83725 | 864 | 11878 |
| next-2 / signature | constant | 0 | 33080 | 10 | 1108 |
| next-2 / hash | quadratic | 9921 | 1329270 | 0 | 482479 |
| next-2 / hash | linear | 8777 | 223218 | 0 | 1330608 |
| next-2 / hash | constant | 0 | 790911 | 0 | 203 |
| next-4 / signature | quadratic | 0 | 66770 | 6950 | 68118 |
| next-4 / signature | linear | 3958 | 83725 | 864 | 11878 |
| next-4 / signature | constant | 0 | 33080 | 10 | 1108 |
| next-4 / hash | quadratic | 12475 | 1573240 | 0 | 526147 |
| next-4 / hash | linear | 9739 | 255420 | 0 | 1451668 |
| next-4 / hash | constant | 0 | 862291 | 0 | 307 |
| mldsa-44 / verifier | quadratic | 1042 | 1513245 | 117963 | 2023851 |
| mldsa-44 / verifier | linear | 181151 | 1947053 | 76124 | 702641 |
| mldsa-44 / verifier | constant | 0 | 31595 | 90634 | 5216 |
| mldsa-65 / verifier | quadratic | 4372 | 1562362 | 144973 | 3081363 |
| mldsa-65 / verifier | linear | 205183 | 2040319 | 94561 | 790236 |
| mldsa-65 / verifier | constant | 0 | 38653 | 91142 | 7024 |

## Compatibility and interpretation

Authenticated inspection verifies that inputs, public inputs, outputs, wires, layers and expanded term counts match the preceding full-class circuits. LFC3 changes the identity domain, so proof-byte differences from prior measurements can result from different Fiat–Shamir queries and Merkle-path overlap. They do not imply a change in round or pad counts.

Relative to the earlier full-class artifacts, NEXT gains 165 raw bytes per bundle, and each ML-DSA circuit gains one raw byte. Decoded NEXT storage falls by 18,584 bytes; ML-DSA falls by 6,464 bytes. Raw, zstd, resident and peak working memory are separate measurements.

Validation: 500 library tests passed, including all saved v1 proof compatibility and circuit-ID checks, native ML-DSA acceptance/corruption tests, and NEXT v9 proofs for two/four attributes. The pre-existing source-inventory test is excluded because of the unrelated untracked streaming.rs. V1 compiler/runtime implementations and frozen artifacts are unchanged. Default and individual-role builds pass. V2 monomial weights are computed iteratively; existing tests compare every prefix against the direct product formula over prime, binary and sextic fields.

## Reproduction

Build timing binaries with:

```sh
cargo build --release --bench mdoc_zk_bench_next --bench mldsa_bench_v2 --features testonly,experimental
```

[run.rs](run.rs) stages binaries, prepares artifacts, performs the rotated timing run and records separate memory samples. Repeat the build with bench-memory for memory binaries. The driver retains caches and logs under /tmp/next-v9-benchmark. [metadata.rs](metadata.rs) verifies circuit IDs, checks unchanged geometry against the previous experiment, and writes size/structure CSVs. Historical comparison inputs remain under /tmp/longfellow-ablation.

Raw observations: [samples](samples.csv), [medians](medians.csv), [sizes](sizes.csv), [memory](memory.csv), [geometry](geometry.csv), [term classes](terms.csv).
