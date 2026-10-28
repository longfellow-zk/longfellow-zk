# Integrated v2 packing: final audit benchmarks

All 14 Cargo benchmark targets completed successfully. Application runs and
Criterion benchmarks were pinned to CPU 2 on an AMD Ryzen 9 9950X; SMT was
enabled and CPU boost disabled. Builds used `target-cpu=native`, release LTO,
`experimental,testonly`, and no allocation instrumentation. Measurements use
one thread. Compilation and offline circuit preparation are excluded; online
circuit/proof decoding, witness generation, setup and cleanup remain included
as defined by each benchmark.

V8 retains unrestricted field-valued hash inputs and therefore uses the identity
adapter with full-width Polygero rows. Its proof size is not comparable to older
V8 measurements that used subfield encoding. V9 uses integrated Boolean packing.

## Applications

V8, V9 and MLDSA entries are medians of three runs. V7 entries are Criterion
central time estimates (10 samples); the two archive encodings prove the same
circuit and produce the same proof length. Every generated application proof
is verified. V9 checks exact proof equality across numerical kernels.

| Application | Prove ms | Verify ms | Proof bytes |
|---|---:|---:|---:|
| MLDSA-44 | 856.502 | 410.992 | 178324 |
| MLDSA-65 | 1021.050 | 484.210 | 187668 |
| Mdoc v8, 2 attributes | 273.435 | 134.704 | 823592 |
| Mdoc v9, 2 attributes, variant 0/window 0 | 191.111 | 94.780 | 184232 |
| Mdoc v9, 4 attributes, variant 0/window 0 | 202.881 | 99.965 | 186824 |
| Mdoc v7, 2 attributes, lfa1 | 521.340 | 249.360 | 360428 |
| Mdoc v7, 2 attributes, lfa2 | 472.730 | 198.110 | 360428 |
| Mdoc v7, 4 attributes, lfa1 | 526.080 | 249.240 | 360428 |
| Mdoc v7, 4 attributes, lfa2 | 471.690 | 198.030 | 360428 |

Raw application logs: [MLDSA](mldsa.log), [V9, 2 attributes](mdoc-v9-2.log),
[V9, 4 attributes](mdoc-v9-4.log), [V8 run 1](mdoc-v8-1.log),
[V8 run 2](mdoc-v8-2.log), [V8 run 3](mdoc-v8-3.log),
[V7, 2 attributes](mdoc-v7-2.log), [V7, 4 attributes](mdoc-v7-4.log).

V9 variant 0 uses the existing SHA arithmetic; variant 1 uses Boolean
arithmetic, and variant 2 also materializes Boolean witness-recipe outputs.
Window 0 selects the reference numerical kernel; 1–4 select the Boolean
kernels. No variant or kernel is selected automatically. All hash inputs,
including MAC masks and reconstructed field values, use the ordinary circuit
input interface and the common zk-v2 packing commitment.

## Polygero witness counts

Counts exclude Polygero's own masking rows.

| Circuit | Logical private inputs | Packed words | Packing masks | GKR pads/products | Polygero witnesses |
|---|---:|---:|---:|---:|---:|
| MLDSA-44 | 161551 | 26926 | 7 | 912 | 27845 |
| MLDSA-65 | 185446 | 30908 | 7 | 912 | 31827 |
| Mdoc v9 hash, 2 attributes | 283468 | 2215 | 129 | 602 | 2946 |
| Mdoc v9 hash, 4 attributes | 309296 | 2417 | 129 | 616 | 3162 |
| Mdoc signature, either size | 3234 | 3234 | 0 | 583 | 3817 |

## All V9 configurations

| Attributes/variant/window | Prove ms | Verify ms | Proof bytes |
|---|---:|---:|---:|
| 2/0/0 | 191.111 | 94.780 | 184232 |
| 2/0/1 | 195.092 | 95.365 | 184232 |
| 2/0/2 | 195.781 | 94.841 | 184232 |
| 2/0/3 | 196.622 | 94.024 | 184232 |
| 2/0/4 | 197.041 | 94.685 | 184232 |
| 2/1/0 | 650.545 | 276.823 | 187912 |
| 2/1/1 | 660.048 | 276.354 | 187912 |
| 2/1/2 | 668.757 | 281.227 | 187912 |
| 2/1/3 | 684.933 | 279.813 | 187912 |
| 2/1/4 | 665.252 | 285.069 | 187912 |
| 2/2/0 | 1140.143 | 779.599 | 212664 |
| 2/2/1 | 1143.209 | 773.630 | 212664 |
| 2/2/2 | 1172.725 | 785.136 | 212664 |
| 2/2/3 | 1172.057 | 780.431 | 212664 |
| 2/2/4 | 1160.602 | 779.898 | 212664 |
| 4/0/0 | 202.881 | 99.965 | 186824 |
| 4/0/1 | 202.373 | 100.265 | 186824 |
| 4/0/2 | 201.876 | 98.955 | 186824 |
| 4/0/3 | 204.663 | 99.666 | 186824 |
| 4/0/4 | 201.365 | 98.854 | 186824 |
| 4/1/0 | 649.564 | 291.217 | 187624 |
| 4/1/1 | 679.641 | 291.876 | 187624 |
| 4/1/2 | 687.060 | 288.482 | 187624 |
| 4/1/3 | 682.481 | 293.193 | 187624 |
| 4/1/4 | 687.422 | 289.537 | 187624 |
| 4/2/0 | 1214.973 | 824.487 | 215768 |
| 4/2/1 | 1219.994 | 821.572 | 215768 |
| 4/2/2 | 1249.358 | 826.572 | 215768 |
| 4/2/3 | 1236.878 | 844.389 | 215768 |
| 4/2/4 | 1237.248 | 832.534 | 215768 |

## Arithmetic and protocol benchmarks

Times below are Criterion's central estimates; raw logs contain confidence
intervals.

| Benchmark | Estimate |
|---|---:|
| [p256_benchmark](p256_benchmark.log): P-256/add | 1.644 ns |
| [p256_benchmark](p256_benchmark.log): P-256/mul | 8.534 ns |
| [p256_benchmark](p256_benchmark.log): P-256/invert | 1.987 µs |
| [q256_benchmark](q256_benchmark.log): Q-256/add | 1.684 ns |
| [q256_benchmark](q256_benchmark.log): Q-256/mul | 16.531 ns |
| [q256_benchmark](q256_benchmark.log): Q-256/invert | 2.032 µs |
| [fft_benchmark](fft_benchmark.log): FFT Forward/256 | 45.020 µs |
| [fft_benchmark](fft_benchmark.log): FFT Forward/1024 | 218.890 µs |
| [fft_benchmark](fft_benchmark.log): FFT Forward/8192 | 2.311 ms |
| [fft_benchmark](fft_benchmark.log): FFT Forward/65536 | 22.867 ms |
| [rfft_benchmark](rfft_benchmark.log): RFFT Forward/256 | 16.598 µs |
| [rfft_benchmark](rfft_benchmark.log): RFFT Forward/1024 | 79.319 µs |
| [rfft_benchmark](rfft_benchmark.log): RFFT Forward/8192 | 839.100 µs |
| [rfft_benchmark](rfft_benchmark.log): RFFT Forward/65536 | 9.378 ms |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/FFT/8 | 2.975 µs |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/IFFT/8 | 2.991 µs |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/BidirectionalFFT/8 | 3.161 µs |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/FFT/12 | 69.734 µs |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/IFFT/12 | 69.760 µs |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/BidirectionalFFT/12 | 70.710 µs |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/FFT/16 | 1.494 ms |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/IFFT/16 | 1.496 ms |
| [lch14_benchmark](lch14_benchmark.log): LCH14 FFT/BidirectionalFFT/16 | 1.486 ms |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/quadratic-extension-fft-v8/prefix/plan | 1.141 ms |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/quadratic-extension-fft-v8/prefix/apply | 783.810 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/quadratic-extension-fft-v8/shifted/plan | 1.082 ms |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/quadratic-extension-fft-v8/shifted/apply | 783.730 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/quadratic-extension-fft-v8/backward/plan | 1.113 ms |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/quadratic-extension-fft-v8/backward/apply | 781.190 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary-v8/prefix/plan | 20.015 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary-v8/prefix/apply | 55.165 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary-v8/shifted/plan | 37.114 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary-v8/shifted/apply | 101.510 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary-v8/backward/plan | 19.994 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary-v8/backward/apply | 55.239 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/scalar/plan | 4.748 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/scalar/apply | 177.360 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/crt-mldsa/prefix/plan | 247.300 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/crt-mldsa/prefix/apply | 903.080 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/crt-mldsa/shifted/plan | 245.030 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/crt-mldsa/shifted/apply | 891.390 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/crt-mldsa/backward/plan | 247.450 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/crt-mldsa/backward/apply | 900.050 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/crt-mldsa/base-inputs/apply | 899.370 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/easy-control/plan | 19.977 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/easy-control/apply | 55.061 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/v8-h/plan | 52.317 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/v8-h/apply | 122.120 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/v8-h-wide/plan | 52.528 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/v8-h-wide/apply | 583.980 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/unbalanced/plan | 42.091 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/unbalanced/apply | 103.740 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/two-large-pieces/plan | 39.346 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/two-large-pieces/apply | 110.710 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/small/plan | 24.575 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/small/apply | 11.384 µs |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/high-boundary/plan | 1.755 ms |
| [range_interpolation_benchmark](range_interpolation_benchmark.log): range/binary/high-boundary/apply | 3.877 ms |
| [sumcheck_bench_v1](sumcheck_bench_v1.log): dense_bind_p256_2e18 | 1.499 ms |
| [sumcheck_bench_v1](sumcheck_bench_v1.log): dense_bind_gf2_128_2e18 | 366.850 µs |
| [sumcheck_bench_v2](sumcheck_bench_v2.log): dense_bind_p256_2e18 | 1.410 ms |
| [sumcheck_bench_v2](sumcheck_bench_v2.log): dense_bind_gf2_128_2e18 | 365.480 µs |

The MLDSA algebra target uses repeated-operation averages rather than Criterion:

```text
ML-DSA algebra benchmark: FFT Fp24/8192=104.725µs; FFT Fp24_6/8192=543.531µs; CRT RS(950,5699)=1.076704ms
```

The Polygero target reports single-run kernel times and proof sizes using
uncertified prototype parameters; these are not application security profiles.
Preprocessing and witness generation are outside its kernel timings.

```text
UNCERTIFIED PROTOTYPE PARAMETERS; kernel timings exclude witness generation and public preprocessing.
binary: config=PolygeroConfig { k: 512, s: 64, n: 8192, t: 64 }, witnesses=8192, preprocessing(two parties)=0.114 ms, commit=15.690 ms, prove=3.400 ms, decode+verify=15.010 ms, proof=93728 bytes
p256: config=PolygeroConfig { k: 512, s: 64, n: 8192, t: 64 }, witnesses=8192, preprocessing(two parties)=0.092 ms, commit=122.197 ms, prove=45.973 ms, decode+verify=320.594 ms, proof=172384 bytes
q256 scalar reference (small workload): config=PolygeroConfig { k: 8, s: 2, n: 64, t: 2 }, witnesses=30, preprocessing(two parties)=0.004 ms, commit=0.341 ms, prove=0.205 ms, decode+verify=0.651 ms, proof=2400 bytes
extension: config=PolygeroConfig { k: 512, s: 64, n: 8192, t: 64 }, witnesses=8192, preprocessing(two parties)=0.099 ms, commit=91.025 ms, prove=33.698 ms, decode+verify=244.853 ms, proof=103616 bytes
```

All process exit codes and elapsed wall times, including offline work, are in
[status.tsv](status.tsv). Pre-audit samples are retained in `pre-audit/` and are
not included in these tables.

## Reproduction

Validation passed 194 selected checks with native limbs and 194 with 32-bit
limbs, including arithmetic, sampling contracts, interpolation and commitment
protocols. The native run includes exact saved-v1-proof compatibility. A further
83 checks passed after cleanup. Raw results: [native](tests-native.log),
[32-bit limbs](tests-limb32.log), [cleanup](tests-cleanup.log),
[all targets](check-all-targets.log), and separate
[prover](check-prover.log), [verifier](check-verifier.log),
[compiler](check-compiler.log) and [data](check-data.log) builds.
The second soundness pass passed [65 focused checks](tests-soundness.log),
including the independent production-compiler residual comparison and the
unsatisfiable all-zero-weight constraint regression. Formatting and local
documentation links were checked. Specifications and Lean sources are unchanged.

From `rust`, build with:

```sh
cargo bench --no-run --features experimental,testonly -j 4 \
  --bench p256_benchmark --bench q256_benchmark \
  --bench fft_benchmark --bench rfft_benchmark --bench lch14_benchmark \
  --bench fp24_benchmark --bench range_interpolation_benchmark \
  --bench sumcheck_bench_v1 --bench sumcheck_bench_v2 --bench polygero_bench \
  --bench mdoc_zk_bench_v1 --bench mdoc_zk_bench_next \
  --bench mdoc_zk_bench_v9 --bench mldsa_bench_v2
```

Use the executable paths printed by Cargo; suffixes depend on build settings.
Run microbenchmarks with `taskset -c 2 <executable> --bench --noplot`. Run
V7 the same way with `MDOC_BENCH_ATTRIBUTES=2` and then `4`. Run MLDSA with
`MLDSA_BENCH_REPEATS=3 taskset -c 2 <mldsa executable> all`. Run V9 with
`MDOC_V9_ATTRIBUTES=2 MDOC_V9_SAMPLES=3 MDOC_V9_CACHE=/tmp/mdoc-cache` and
then attributes `4`; leave `MDOC_V9_QUICK` unset for the full matrix. Run V8
three times, saving its offline archive once with `MDOC_BENCH_SAVE_ARCHIVE`
and loading it subsequently with `MDOC_BENCH_ARCHIVE`.

The [implementation audit](../../../runtime/dual-packing/AUDIT.md) records
correctness checks, masking-basis validation, ownership cleanup, and the limits
of the existing formal security results. This audit changes neither sampling
nor specification documents.
