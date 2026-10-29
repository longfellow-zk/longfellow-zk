# Longfellow ZK (Rust Implementation)

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](../LICENSE)
[![IETF Draft](https://img.shields.io/badge/IETF%20Draft-draft--google--cfrg--libzk-lightgrey)](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/)

This directory contains the Rust implementation of the Longfellow
Zero-Knowledge (ZK) proof system. It remains under development.

The major problem with the C++ implementation was the confusing
organization of circuits.  We believe that this implementation is a
major improvement on this front.  We have reworked all circuits in
units with cleanly defined interfaces and extensive tests.  The Rust
type system helps with keeping circuits well-structured and organized,
as opposed to the old C++ templates.  The new compiler supports
rudimentary debug symbols so that one can assert that an invalid input
triggers the exact assertion that is expected to catch that case (as
opposed to a generic "some assertion has failed" of the old system).

All circuits, but especially the mdoc-zk circuits, have been reworked
to be much more stringent.  They perform paranoid checks on all
inputs, irrespective of whether they are necessary or not.  We have
organized the code to maximize local auditability as opposed to
circuit size.

In the original comparison with the C++ compiler, the full mdoc-zk
circuits were about 10% smaller despite performing more checks.

We have also rewritten the runtime portion (the prover and verifier)
in Rust. In the measurements behind this rewrite, performance was
comparable to the C++ implementation and the Rust prover used less than
100MB to produce a proof for the full mdoc-zk circuits, versus about
170MB for the then-current C++ prover and about 600MB for the initial
2025 prover. These are historical measurements, not current guarantees.

We have defined a circuit format called LFC2 that is more compact than
the C++ format (retroactively named LFC1). In the original mdoc-zk
comparison, LFC2 circuits occupied about 1MB before zstd compression,
versus about 100MB for LFC1.

The implementation includes an LFC1 reader to support the C++ circuit
format. Its intended compatibility includes bit-for-bit equal proofs
for matching circuits and prover randomness.

We are also switching to a new development model.  In the past, the
source of truth was an internal Google repository, with periodic
pushes to github from us (Google).  Going forward, the source of truth
will be github and Google will periodically import github as needed.
This switch will make it easier for us to accept third-party
contributions.

The older C++ implementation remains in [`../lib`](../lib); this Rust
workspace does not contain a separate C++ runtime for its new circuits.

---

## Longfellow v1 and v2

**Longfellow v1 is the deployed version.** It uses sumcheck and Ligero.
The Rust v1 implementation is 100% compatible with the C++ code. It supports
the same frozen mdoc circuits and preserves their circuit IDs, transcript
behavior, and proof encoding.

**Longfellow v2 is still evolving and is not final.**
It introduces projective sumcheck and replaces Ligero with nonrecursive
Polygero. V1 remains supported alongside this development.

In particular, the Fiat–Shamir transcript will change to conform to the CFRG
[Fiat-Shamir Transformation specification](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/),
currently `draft-irtf-cfrg-fiat-shamir-03` (an Internet-Draft, not yet a published
RFC).

Polygero is described in
[Polygero: Proximity Testing From Polynomial Challenges](https://eprint.iacr.org/2026/2481)
by Matteo Frigo and abhi shelat.

| | Longfellow v1 | Longfellow v2 |
|---|---|---|
| Status | Deployed | Under development |
| Commitment protocol | Ligero | Nonrecursive Polygero |
| Combined proof implementation | `runtime::zk_v1` | `runtime::zk_v2` |
| mdoc application API | `mdoc::v1` | `mdoc::v2` |
| mdoc circuits | Frozen versions 5–7 | NEXT, version 9 |

Circuit versions have their own numbering: circuit v7 uses Longfellow v1,
while NEXT circuit v9 uses Longfellow v2.

Tests reproduce all twelve saved v1 proofs bit for bit using the same
inputs and prover randomness. V2 circuits, parameters, and proof encoding
remain subject to change. There are currently no frozen v2 mdoc circuits.

## Performance

The [formal v1 analysis](../formal/lfzk-v1/README.md) establishes **116-bit
Fiat–Shamir T-security** for the modeled v7 composition, under its documented
assumptions. The [formal v2 composition](../formal/lfzk-v2/README.md) proves
**117-bit extraction security** for the modeled authenticated
two-field verifier: `Pr[accept ∧ extraction fails] ≤ (1+N+tA)/2^117`.
The bound holds for all query budgets, and the circuit/MAC correspondence and
ideal-sampler premises are documented in the [audit](../formal/AUDIT.md).
Complete V2 joint-view zero knowledge is not yet proved. For the current Polygero parameters,
the [checked component certificates](../formal/parameters/polygero/PolygeroRustHahn.lean)
establish **127 bits** for the hash/signature profiles in the ideal-binding, uniform-sampler
Fiat–Shamir model. This component bound excludes the Merkle binding reduction
and the rest of the Longfellow v2 composition.
NEXT v9's packed composition is outside these component theorems.

The following measurements cover a complete mdoc presentation disclosing
two attributes, including both the hash and signature proofs.

| Version | Circuit | Proving | Verification | Complete proof | Prover peak heap | Verifier peak heap |
|---|---|---:|---:|---:|---:|---:|
| Longfellow v1 | v7 | 467 ms | 196 ms | 360,428 bytes | 104.1 MiB | 45.1 MiB |
| Longfellow v2 | NEXT v9 | 167 ms | 88 ms | 185,576 bytes | 43.2 MiB | 34.5 MiB |

The experimental ML-DSA verifier circuits use v2/Polygero separately from
the mdoc application. These runs are outside the 117-bit two-field theorem
above.

| Circuit | Proving | Verification | Complete proof | Prover peak heap | Verifier peak heap |
|---|---:|---:|---:|---:|---:|
| ML-DSA-44 | 621 ms | 290 ms | 178,964 bytes | 101.4 MiB | 38.3 MiB |
| ML-DSA-65 | 717 ms | 339 ms | 188,180 bytes | 106.4 MiB | 43.7 MiB |

NEXT and ML-DSA measurements were rerun on 2026-10-29 using three-stream LFC3
and a private per-layer split in sumcheck v2, Rust 1.99.1 release builds with
`target-cpu=native` on an AMD Ryzen 9 9950X
with boost disabled. Times are medians of seven samples after warmup, pinned to
one CPU, after builds and tests finished. NEXT uses compressed LFA2 archives.
The [current report](benches/results/2026-10-29-layer-split/README.md) includes
raw/zstd sizes, decoded memory, term breakdowns, and all samples. The v1 row
retains its 2026-10-26 Criterion mean from ten samples, recorded in the
[historical run data](benches/results/2026-10-26.json).

Peak heap is the additional live Rust heap allocation during each operation,
measured in separate runs with `bench-memory` enabled. It excludes allocations
already present at entry, allocator overhead, and stack memory; it is not
total process RSS. One MiB is 1,048,576 bytes.

Online timings include circuit decoding, native input preparation,
commitment, proof encoding or decoding, and cleanup. Inputs are already
memory-resident. Offline circuit compilation and parameter selection are
excluded.

The comparison includes changes to both the circuit and the proof protocol.

## Architecture

The ZK implementation coordinates commitment and sumcheck. Sumcheck reduces
circuit satisfaction to constraints on committed witnesses and masking
values. A runtime constraint compiler translates those results into the
equations checked by Ligero or Polygero.

The runtime constraint compiler is separate from the offline circuit
compiler. Proving and verification do not require the `compiler` feature.

V1 and v2 implementations occupy separate directories and have their own
application types, specifications, transcripts, and proof codecs. They share
basic infrastructure such as arithmetic, interpolation, randomness, and
Merkle trees.

Sumcheck does not depend on Ligero, Polygero, or the combined ZK
implementation. The top-level dependency checker enforces these boundaries,
including code behind inactive feature gates.

### Source layout

This is one Cargo crate, `longfellow-zk`. The directories organize modules;
they are not separate crates.

| Directory | Contents |
|---|---|
| `core/` | Basic algebra interfaces, circuit representations, and circuit serialization |
| `compile/` | Symbolic arithmetic, circuit compilation, and offline parameter selection |
| `runtime/` | Concrete arithmetic, interpolation, proof protocols, and proof serialization |
| `circuits/` | Reusable circuit components and native witness generation |
| `applications/mdoc_zk/` | mdoc circuits, application APIs, specifications, providers, and artifacts |
| `tools/` | Rust commands for parameter auditing and specification generation |
| `src/lib.rs` | Module assembly and feature gates |
| `src/dependency_tests.rs` | Dependency and source-organization checks |

Compile-time and runtime code occupy separate directories. Prover and
verifier implementations also remain separate within each protocol.

The circuit compiler has v1 and v2 backends. The v1 backend preserves
historical Morton ordering and circuit IDs.

Formal proofs and parameter certificates live in [`../formal`](../formal),
including `../formal/parameters`. There are no Lean source files in the
Rust directory.

## Circuits, specifications, and providers

Applications select `mdoc::v1` or `mdoc::v2`. Each provides
`run_mdoc_prover`, `run_mdoc_verifier`, and its own `ZkSpecStruct`.

A specification identifies a circuit and fixes its commitment parameters.
The prover and verifier use the same specification and matching archive.

For v2, the hash and signature components each have independent
`(K, N, s, T)` parameters:

| Parameter | Meaning |
|---|---|
| `K` | Polynomial dimension: K samples represent degree strictly below K |
| `N` | Number of oracle columns |
| `s` | Batching-polynomial degree bound |
| `T` | Number of opened columns and random prefix samples per row |

Offline parameter selection lives in `compile::polygero`. The selected
parameters are saved in the specification. Provers and verifiers derive
the remaining geometry deterministically; they do not tune parameters.

### Frozen circuits and NEXT

The runtime providers load registered frozen circuits without invoking
a compiler. Unknown specifications and missing artifacts are errors.

`mdoc::development_provider` handles development use. It delegates frozen
requests to the runtime providers and compiles explicit development requests.
The result contains the circuit archive and its matching specification.

NEXT currently denotes circuit version 8. It is under development and is
not in the frozen registry. Saving a NEXT bundle preserves both its circuit
and its selected parameters.

Freezing a circuit requires publishing its archive, complete specification,
and compatibility fixtures. Frozen artifacts and parameters remain
unchanged. Development of a subsequent version uses an explicit versioned request.

Circuit archives are trusted inputs. The v2 loader supports optional
circuit-ID recomputation through `enforce_circuit_id`.

### NEXT v9

NEXT is v9, executed through `mdoc::v2`. There is one compiler configuration:
compact analog arithmetic with direct Boolean hash inputs. The hash commitment
packs these bits into GF128 elements; the P256 signature component keeps its
field-valued input convention. Neither circuit contains a One wire.

The LFA2 bundle contains the signature circuit, hash circuit, and an authenticated
`hash-input` manifest. Both circuits use LFC3's three streams. Bundle and cache
creation verify payload IDs; runtime invocations validate the manifest and declared
identities under the existing trusted-archive contract. The hash circuit checks
its MAC equations on reconstructed bit inputs.

`development_provider::compile_next(count)` compiles the default circuit and selects
parameters offline. `read_next` / `write_next` preserve that complete specification.
V8 and alternative v9 compiler/witness configurations are not supported.

The benchmark prints raw samples. Keep allocation tracking disabled for timings
and enable it separately for heap measurements:

```sh
MDOC_V9_SAMPLES=7 MDOC_V9_ATTRIBUTES=2 MDOC_V9_CACHE=/tmp/next-v9 \
  taskset -c 2 cargo bench --bench mdoc_zk_bench_next --features testonly
# Repeat with MDOC_V9_ATTRIBUTES=4. Add bench-memory only for heap measurements.
```

See the [current NEXT/ML-DSA benchmark](benches/results/2026-10-29-next-v9/README.md)
for raw/zstd sizes, proof bytes, term counts, times and memory.


## Cargo features

Features support builds tailored to the prover, verifier, or offline
compiler. The default features are `verifier`, `prover`, `compiler`, and
`mdoc`.

| Feature | Purpose |
|---|---|
| `verifier` | Runtime proof verification |
| `prover` | Witness generation and runtime proving |
| `compiler` | Symbolic construction, circuit compilation, and parameter selection |
| `mdoc` | mdoc application and circuit-archive support |
| `experimental` | Additional arithmetic and circuits under development |
| `testonly` | Test fixtures and deterministic randomness; also enables both proof roles and the compiler |
| `tooling` | Offline Rust tools, including compiler and experimental-arithmetic dependencies |
| `bench-memory` | Benchmark allocation tracking |
| `bench-profile` | Opt-in execution-phase diagnostics; disable for ordinary timing comparisons |

V2 itself does not require `experimental`. Neither `experimental` nor
`tooling` is enabled by default. The `tooling` feature does not enable
proving or verification.

Feature gates are placed high in the module tree. The `cfg_compiler!`,
`cfg_prover!`, `cfg_verifier!`, `cfg_prover_or_compiler!`, and
`cfg_testonly!` macros in `src/lib.rs` group conditional declarations.

## Building and testing

Run commands from this directory. Normal builds use stable Rust.
Repository formatting uses nightly Rust.

```sh
# Default build.
cargo build --release

# Application verifier without the prover or compiler.
cargo build --release --no-default-features --features verifier,mdoc

# Application prover without the verifier or compiler.
cargo build --release --no-default-features --features prover,mdoc

# Offline application compiler.
cargo build --release --no-default-features --features compiler,mdoc

# Standard test suites.
cargo test --release --features testonly

# Include experimental components.
cargo test --release --features testonly,experimental

# Offline-tool tests without proof-role features.
cargo test --no-default-features --features tooling --bin zk_tool
```

Shared compiler and circuit suites exercise compile_v2 and LFC3. Dedicated compatibility tests exercise compile_v1.
V1 tests verify saved proofs and reproduce their exact bytes. V2 tests
cover successful proofs, rejected statements, and malformed proofs.

Standalone `prover_only` and `verifier_only` programs demonstrate v1 mdoc
execution with separate feature builds. Run either with `--help` for
circuit-file options.

## Benchmarks

```sh
# V1 with circuit v7 and two attributes, using an LFA2 archive.
MDOC_BENCH_ATTRIBUTES=2 \
  cargo bench --bench mdoc_zk_bench_v1 --features testonly -- lfa2

# V2 with NEXT v9 and two attributes.
cargo bench --bench mdoc_zk_bench_next --features testonly

# Experimental packed ML-DSA-44 and ML-DSA-65, three runs per circuit.
MLDSA_BENCH_REPEATS=3 \
  cargo bench --bench mldsa_bench_v2 --features testonly,experimental
```

The MLDSA v2 benchmark packs six private prime-field inputs into each sextic
field word before Polygero commitment, using the existing circuit and witness
generator. Both applications use ordinary zk-v2. See the
[integration benchmark comparison](benches/results/2026-10-28-integrated-packing/README.md).

The NEXT benchmark can save a specification/archive bundle using
`MDOC_BENCH_SAVE_ARCHIVE`, or load one using `MDOC_BENCH_ARCHIVE`.
Loading a bundle preserves its saved parameters.
Repeat the NEXT run three times for the reported median; subsequent runs
can load the bundle saved by the first run.

Timing and allocation tracking run separately. Add `bench-memory` for
memory measurements. It reports peak additional Rust heap, excluding
already-resident input buffers; it does not measure process RSS.
Keep allocation tracking disabled for timing comparisons.

## Offline tools

Parameter selection belongs to the compiler. The standalone `zk_tool`
provides:

| Command | Purpose |
|---|---|
| `check-profiles` | Check parameter budgets with exact arithmetic, optionally using Lean |
| `certify-hahn` | Check Hahn packing certificates with Lean |
| `generate-v2-specs` | Compile NEXT and print candidate specifications for review |

Formal checking reads proof sources from the selected formal project,
normally `../formal`. Normal Rust builds, parameter selection, proving,
and verification do not require the Lean toolchain.

Parameter certificates establish mathematical bounds under their stated
assumptions; they do not certify the complete Rust implementation.

The tools are written in Rust. Python is not required.

## Development conventions

Keep compiler, prover, and verifier responsibilities explicit. Preserve
v1 compatibility while developing v2.

Tests belong outside production source files. Register new files in the
top-level dependency checks.

Before every commit, run:

```sh
cargo +nightly fmt
```

## Known limitation

NEXT mdoc checks that requested namespace IDs agree with each other,
but the circuit does not authenticate those namespace IDs. Changing all
requested namespace IDs can leave a proof valid. This remains unresolved.

## License

Licensed under the Apache License, Version 2.0.
See [LICENSE](../LICENSE) for details.

### Circuit compilers and formats

`compile_v1` preserves the historical compiler, input convention and LFC1/LFC2
encoding used by frozen v5–v7 circuits. `compile_v2` emits native v2
[LFC3](core/proto/LFC3.md) circuits with three independently compressed streams
per layer and no One wire. Both circuit formats fit inside the existing LFA2
archive container. Shared compiler/circuit tests use LFC3; dedicated v1
compatibility tests retain legacy fixtures and byte hashes.

Sumcheck v2 privately splits each layer's stored segments into eleven working
streams once, using coefficient indices 0, 1 and 2. Bindings traverse each class
independently. Source circuits remain read-only; token arrays are borrowed and
repeated segments are not expanded.

The earlier [class ablation](benches/results/2026-10-29-class-ablation/README.md)
records the retired eleven-stream implementation. Current LFC3 has three streams
and implicit coefficient slots 0, 1 and 2 for 0, 1 and -1.
Benchmarks print quadratic, linear and constant counts, including assertion and coefficient-value breakdowns.
