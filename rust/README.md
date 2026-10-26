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
| mdoc circuits | Frozen versions 5–7 | NEXT, currently version 8 |

Circuit versions have their own numbering: circuit v7 uses Longfellow v1,
while NEXT circuit v8 uses Longfellow v2.

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
The experimental packed-v9 composition is outside these theorems.

The following measurements cover a complete mdoc presentation disclosing
two attributes, including both the hash and signature proofs.

| Version | Circuit | Proving | Verification | Complete proof | Prover peak heap | Verifier peak heap |
|---|---|---:|---:|---:|---:|---:|
| Longfellow v1 | v7 | 467 ms | 196 ms | 360,428 bytes | 104.1 MiB | 45.1 MiB |
| Longfellow v2 | NEXT v8 | 269 ms | 131 ms | 213,204 bytes | 74.8 MiB | 38.3 MiB |

The experimental ML-DSA verifier circuits use v2/Polygero separately from
the mdoc application. These runs are outside the 117-bit two-field theorem
above.

| Circuit | Proving | Verification | Complete proof | Prover peak heap | Verifier peak heap |
|---|---:|---:|---:|---:|---:|
| ML-DSA-44 | 923 ms | 608 ms | 178,338 bytes | 114.8 MiB | 39.2 MiB |
| ML-DSA-65 | 1,081 ms | 701 ms | 188,386 bytes | 121.9 MiB | 43.0 MiB |

Measurements were rerun on 2026-10-26 using Rust 1.99.1 release builds
with `target-cpu=native` on an AMD Ryzen 9 9950X with boost disabled.
Benchmarks ran sequentially after builds and tests finished. The mdoc
comparison uses compressed LFA2 archives. V1 timings are Criterion means
from ten samples; v2 and ML-DSA timings are medians of three runs.
The [run data](benches/results/2026-10-26.json) includes individual timings,
exact heap counts, parameter profiles, and circuit/proof fingerprints.

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

### Experimental packed v9

With `experimental`, `CircuitRequest::PackedV9 { num_attributes }` compiles
a separate v9 bundle. NEXT remains v8. The paired API is
`mdoc::v2::packed_v9`; its specification and cache are separate types/formats.

V9's hash circuit takes logical bits and commits polynomial-basis GF128 packed
words. Its canonical `hash-input` manifest is the third archive entry and
participates in the combined identity. Bundle creation/cache loading verifies
circuit payload IDs; runtime invocations use the same trusted-archive premise
as v8 and check the manifest and declared identities. Six polynomial-basis
MAC equations are combined after hash GKR and reduced with the final input claim by
[standalone flat trace ring switching](runtime/ring-switch/README.md). It uses
127 masked response fields and 128 committed mask/checksum cells, with no
tower construction or inner sumcheck. The hash proof
uses `LFB2`; the signature proof retains `LFV2`.

`compile_packed_v9_variant(count, variant)` exposes the measured alternatives:
0 is compact analog arithmetic, 1 is Boolean carry-save arithmetic, and 2
uses additional Boolean partial-sum witnesses with local carry checks.
Each variant gets its own manifest, circuit identity and parameters.
`run_mdoc_prover_inner_with_window` selects the reference prover (`None`)
or Boolean windows 1–4; fixed randomness produces identical proof bytes
within a compiler variant. No variant is selected automatically.

This is a Rust prototype. The existing v8 security bound does not cover the
new ring-switch composition. Joint zero knowledge, composed Fiat–Shamir
soundness, and Lean formalization remain open gates before production use.

The v9 benchmark emits interleaved raw CSV samples and reports medians.
Use a single pinned CPU, keep allocation tracking off for timing, and run
heap measurements separately:

```sh
MDOC_V9_SAMPLES=3 MDOC_V9_ATTRIBUTES=2 MDOC_V9_CACHE=/tmp/mdoc-v9-flat \
  taskset -c 2 cargo bench --bench mdoc_zk_bench_v9 --features testonly,experimental
# MDOC_V9_QUICK=1 selects only the compact reference case.
# Repeat with MDOC_V9_ATTRIBUTES=4; add bench-memory only for separate heap runs.
```

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

Shared compiler and circuit suites exercise both compiler backends.
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

# V2 with NEXT v8 and two attributes.
cargo bench --bench mdoc_zk_bench_next --features testonly

# Experimental ML-DSA-44 and ML-DSA-65, three runs per circuit.
MLDSA_BENCH_REPEATS=3 \
  cargo bench --bench mldsa_bench_v2 --features testonly,experimental
```

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
