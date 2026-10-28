# Generic packing and ambient-only V2 backend

Single-thread full mdoc v9, variant 0, reference numerical kernel, pinned to CPU 2.
Each row is the median of three fixed-seed samples. All six proofs verified.
Circuit compilation/cache generation occurs before the timed calls; runtime
loading and protocol setup remain included, matching the existing benchmark.

| Attributes | Prove ms | Verify ms | Proof bytes |
|---:|---:|---:|---:|
| 2 | 214.067 | 122.255 | 185640 |
| 4 | 229.152 | 131.951 | 187336 |

Raw samples: [two attributes](v9-2-final.log), [four attributes](v9-4-final.log).
The preceding trace-zero report measured 206.331/116.865 ms and
222.007/126.540 ms respectively, with 185268 and 187476 bytes. Those are
historical measurements, rather than an interleaved regression comparison.
The new backend codec and transcript context change the complete proof bytes
and Merkle frontier. The binary packing messages themselves remain byte-for-byte
identical to the generic reference for the same inputs and randomness.

Build and run from `rust`:

```sh
cargo bench --bench mdoc_zk_bench_v9 --features experimental,testonly --no-run
MDOC_V9_QUICK=1 MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=2 \
  MDOC_V9_CACHE=/tmp/longfellow-generic-packing-cache \
  taskset -c 2 target/release/deps/mdoc_zk_bench_v9-cfbe2b4d7e8783bf
MDOC_V9_QUICK=1 MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=4 \
  MDOC_V9_CACHE=/tmp/longfellow-generic-packing-cache \
  taskset -c 2 target/release/deps/mdoc_zk_bench_v9-cfbe2b4d7e8783bf
```

The executable suffix depends on build settings. `QUICK=1` selects only variant
0/window 0; the benchmark still evaluates the complete application, including
signature verification and both commitment backends. This report does not
remeasure the Boolean compiler variants or alternative numerical kernels.

The generic protocol is independently exercised over GF128/GF2, GF128/GF256,
small odd-characteristic fields, and the sextic MLDSA extension, with identity
packing over P256. Owned basis initialization can be performed once and reused
before protocol invocations. Tests check native equations against the original
Polygero commitment, sparse-codec sampling, byte/transcript equivalence for the
binary specialization, degree-one bypass and exhaustive GF9 false-claim counts.
See the [protocol README](../../../runtime/dual-packing/README.md).
