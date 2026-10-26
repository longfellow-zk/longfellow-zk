# Flat-trace v9 benchmark, 2026-10-26

Two attributes; compact analog compiler and reference numerical kernel.
Three pinned-CPU samples, with allocation tracking disabled.

The later dense-transpose optimization retains one-hand GKR and produces
exactly the same proof bytes. Its three-sample medians are **209.352 ms
prover**, **122.446 ms verifier**, **185,268 B**. The separately profiled
ring-switch phase falls from **46.488 ms to 8.022 ms** on the prover;
the verifier phase is 4.791 ms (previously 4.504 ms). The main improvement
is in prover computation. The isolated response computation falls from
about 42.1 ms to 1.63 ms on the same public coefficients and random bits.

Updated raw samples: [xor-v9.csv](xor-v9.csv), [xor-v9.log](xor-v9.log).
Phase samples: [xor-profile.csv](xor-profile.csv),
[xor-profile.log](xor-profile.log). Build details and the byte-identical
proof digest are in [xor-metadata.json](xor-metadata.json).
Exact reference-formula tests pass for every response component, partial
packed words, and both native and generic field implementations.

The measurements below record the earlier dense implementation.
The final implementation checks and compatibility fingerprints are recorded
in [audit.txt](audit.txt).

| Version | Median prover | Median verifier | Proof |
|---|---:|---:|---:|
| Flat-trace v9 | 249.555 ms | 121.203 ms | 185,268 B |
| NEXT v8 | 267.969 ms | 129.833 ms | 213,204 B |

V9 reduces proof bytes by 13.10%.
The unchanged v8 proof SHA256 is recorded in the raw logs and metadata.

Online timings include circuit/proof decoding, native preparation,
commitments, proving, serialization, verification and cleanup as appropriate.
Offline compilation, parameter selection and bundle validation are excluded.
Both runtimes assume trusted circuit archives.

The adapter uses 127 response fields (2032 bytes), 127 independent masks
and one checksum cell, one native linear equation, and no additional
multiplication constraints or roots. It uses no tower construction or inner
sumcheck. V9 is experimental; its composed security proof remains deferred.

Machine/build details are in [metadata.json](metadata.json).
Raw v9 samples are in [v9.csv](v9.csv); v8 samples are in
[v8-1.log](v8-1.log), [v8-2.log](v8-2.log), [v8-3.log](v8-3.log).

Reproduce the v9 case with:

```sh
MDOC_V9_QUICK=1 MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=2 \
MDOC_V9_CACHE=/tmp/mdoc-v9-flat taskset -c 2 \
  cargo bench --bench mdoc_zk_bench_v9 --features testonly,experimental
```

These measurements cover this one explicit variant. No compiler or numerical
kernel is promoted automatically.



Circuit sizes for the same two-attribute fixtures:

| Hash circuit metric | V8 | V9 |
|---|---:|---:|
| Layers | 20 | 20 |
| Wires across layers | 3,473,933 | 2,350,677 |
| Quadratic terms | 6,394,835 | 4,183,645 |
| Committed field cells | 77,410 | 2,945 |

V9's committed cells are 2,209 packed inputs, six MAC pads, 128 adapter cells
and 602 GKR pad/product cells. Both hash circuits have 20 GKR product
constraints. The signature circuit has the same ID in both bundles.

Phase diagnostics are in [profile.json](profile.json) and
[profile.log](profile.log). Three runs used the opt-in `bench-profile` feature.
The run with median total prover and verifier time had:

| Phase | Prover | Verifier |
|---|---:|---:|
| Hash GKR and statement | 120.3 ms | 60.8 ms |
| Ring switching | 46.4 ms | 4.5 ms |
| Signature GKR and constraints | 33.9 ms | 9.8 ms |
| Polygero backends | 11.0 ms | 33.4 ms |
| Commitments | 22.9 ms | — |
| Setup, claims, I/O and cleanup | 12.7 ms | 12.2 ms |
| Total | 247.1 ms | 120.8 ms |

The hash GKR interval includes evaluation and statement binding; the backend
intervals include their local cleanup. Diagnostic instrumentation is disabled
in the ordinary timing measurements above.

The [factoring diagnostic](factoring.txt) finds rank 128 in the actual
terminal GKR coefficient matrix, with and without the MAC equations. The
paper's small-tensor optimization does not apply directly. The dense binary
transpose described in the [adapter documentation](../../../runtime/ring-switch/README.md)
accelerates these full-rank coefficients while retaining one-hand GKR.
