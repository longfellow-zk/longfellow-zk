# Full mdoc and MLDSA benchmarks

AMD Ryzen 9 9950X, frequency boost disabled, release build with `target-cpu=native`.
Runs were sequential and pinned to logical CPU 2. Median of three samples;
allocation tracking disabled. Times include the complete online prover/verifier
operations and exclude circuit compilation. All twelve proofs verified; the
MLDSA benchmark also rejected a changed public key outside the timed operations.

| Application | Prove ms | Verify ms | Proof bytes |
|---|---:|---:|---:|
| mdoc v9, 2 attributes | 214.101 | 122.649 | 185640 |
| mdoc v9, 4 attributes | 228.582 | 131.268 | 187336 |
| MLDSA-44 | 1095.608 | 625.733 | 523830 |
| MLDSA-65 | 1237.434 | 708.188 | 583638 |

mdoc uses packed v9, compiler variant 0 and reference numerical kernel
(`MDOC_V9_QUICK=1` selects this configuration; it does not reduce application
work). MLDSA v2 uses the ordinary unpacked sextic-field path and ambient-field
Polygero row encoding. Both MLDSA parameter sets selected
`k=1024, s=25, n=4096, t=128`.

Offline preparation took 13.596 s for MLDSA-44 and 15.836 s for MLDSA-65,
including circuit compilation, serialization and parameter selection.

Raw results: [mdoc, two attributes](mdoc-v9-2.log),
[mdoc, four attributes](mdoc-v9-4.log), [MLDSA](mldsa-v2.log).

Commands, from `rust` (executable suffixes depend on build configuration):

```sh
cargo bench --bench mdoc_zk_bench_v9 --bench mldsa_bench_v2 --features experimental,testonly --no-run
MDOC_V9_QUICK=1 MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=2 MDOC_V9_CACHE=/tmp/longfellow-generic-packing-cache taskset -c 2 target/release/deps/mdoc_zk_bench_v9-cfbe2b4d7e8783bf
MDOC_V9_QUICK=1 MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=4 MDOC_V9_CACHE=/tmp/longfellow-generic-packing-cache taskset -c 2 target/release/deps/mdoc_zk_bench_v9-cfbe2b4d7e8783bf
MLDSA_BENCH_REPEATS=3 taskset -c 2 target/release/deps/mldsa_bench_v2-61ee897a1fe800ff all
```
