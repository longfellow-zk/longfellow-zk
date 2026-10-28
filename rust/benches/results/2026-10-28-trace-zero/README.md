# Trace-zero dual packing, 2026-10-28

The main paper's Artin–Schreier protocol replaces the previous GF128
Frobenius-orbit adapter. The new adapter authenticates two linear equations,
uses 129 committed cells and sends 129 field elements (2064 bytes). There is
no new multiplication gate or commitment root. The old adapter used 128 cells,
127 response elements and one linear equation.

These are complete v9 mdoc timings, including the unchanged signature path.
The compact circuit with the reference numerical kernel gives these medians:

| Attributes | Before prove | After prove | Before verify | After verify | Before proof | After proof |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 213.264 ms | 206.331 ms | 121.459 ms | 116.865 ms | 185,332 B | 185,268 B |
| 4 | 223.733 ms | 222.007 ms | 128.787 ms | 126.540 ms | 187,028 B | 187,476 B |

The change gives a modest timing improvement in these samples, not a large
speedup. Three samples per configuration are insufficient to establish small
differences robustly. The earlier quick run's 200.693/114.380 ms for two
attributes is superseded by the full interleaved sweep above.

The raw adapter response grows by 32 bytes. Complete proof size also changes
with Merkle multiproof path sharing because the masks and transcript change
the opening queries. The smaller two-attribute proof does not establish a
structural proof-size saving.

## Method and complete data

Baseline source is v2 commit `c36f807`; the after measurement uses the working
tree implementation. Both release executables were built from the Rust
workspace using `target-cpu=native`, opt-level 3, LTO and one codegen unit,
with rustc 1.99.1 / LLVM 23.1.1. Host: AMD Ryzen 9 9950X, boost disabled.
Each executable ran single threaded on CPU 2, serially, without heap or phase
instrumentation and without concurrent compilation.

All three compiler variants and all five numerical kernels were measured with
two and four attributes, three samples each: 90 baseline proofs and 90 new
proofs. Every proof verified; fixed-seed proof bytes matched across all five
kernels within each compiler variant. The benchmark rotates execution order
between samples. Variant 0 is compact analog arithmetic, variant 1 Boolean
carry-save arithmetic, and variant 2 Boolean partial-sum witnesses with local
carry checks. Window 0 is the reference kernel; windows 1–4 are explicit
Boolean kernels.

The [complete median table](medians.md) includes every configuration. Raw
samples are [before, two attributes](before-v9-2.log),
[after, two attributes](after-v9-2.log),
[before, four attributes](before-v9-4.log), and
[after, four attributes](after-v9-4.log).

The old and new development caches were compared byte for byte after their
eight-byte version markers. All six pairs have identical circuit identities,
parameters, manifests and compressed circuit payloads; see
[cache-check.log](cache-check.log). The new files were generated through the
new compiler/provider, without relabelling old caches.

From `rust`, build and rerun the new measurements:

```sh
cargo bench --bench mdoc_zk_bench_v9 --features experimental,testonly --no-run
MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=2 MDOC_V9_CACHE=/tmp/longfellow-tracezero-v9-cache \
  taskset -c 2 target/release/deps/mdoc_zk_bench_v9-cfbe2b4d7e8783bf
MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=4 MDOC_V9_CACHE=/tmp/longfellow-tracezero-v9-cache \
  taskset -c 2 target/release/deps/mdoc_zk_bench_v9-cfbe2b4d7e8783bf
```

The executable suffix depends on the build environment. Baseline measurements
used the separately saved executable `/tmp/mdoc-v9-before-tracezero` and
`MDOC_V9_CACHE=/tmp/longfellow-flat-v9-cache`, with the same samples, attribute
counts and CPU affinity.

## Audit and validation

The [implementation audit](../../../runtime/dual-packing/AUDIT.md) maps the
paper's native equations to the adapter, transcript and Polygero rows. It also
records the reserved-One validation bug found and fixed during the audit.
Independent oracles compare both expanded equations with literal paper
equations for arbitrary committed cells, including inconsistent b and false
targets. Other tests cover completeness, transcript order, malformed messages,
codecs, hidden affine targets, original-commitment indexing, all v9 compiler
variants, cache round trips, old-format rejection and Boolean proof equality.

[verification.log](verification.log) records the passing test suites, feature
checks and release rebuild. [clippy.log](clippy.log) records the final library
and test lint check; its warnings are pre-existing and outside the changed
files. Nightly rustfmt and whitespace checks pass. No Lean sources were changed
or rebuilt, and this report makes no new composed soundness or joint
zero-knowledge claim.
