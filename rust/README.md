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
Polygero. A fresh challenge at each sumcheck terminal makes all commitment
constraints linear, eliminating Polygero's product-copy rows. V1 remains supported.
V1 retains its SHA-256 transcript accumulator and AES-256 challenge generator.
V2 uses a direct SHAKE256 transcript with explicit message and challenge phases.
Each round finalizes a private accumulator snapshot, absorbs the first 32 output
bytes as a link, and draws challenges from the remaining output of that same
SHAKE reader. Empty rounds also bind a round label and counter. Intermediate
links stay internal; complete proofs end with a 32-byte seal over the chained
transcript and actual canonical proof body, including terminal authentication.

V2 callers receive separate writing and reading capabilities. `begin_squeeze` consumes
the writer; closing the reader returns the round-completion token. Public
cloning, resetting, raw-state access, and use as private prover randomness are
unavailable. Complete-proof encoders own finalization, and decoding returns
immutable unverified data. Only complete verification returns `VerifiedProof`
evidence after checking the seal.

The [witness-selection protocol](runtime/v2/witness-selection/README.md) wraps the
joint commitment before either mdoc sumcheck. Each field commits two dedicated
mask cells, receives two independent full coefficient vectors, and sends two
masked dot products. Its opaque state automatically adds both affine equations
to the later Polygero statement. These cells are backend auxiliaries, not
field-valued inputs to the binary circuit.

In particular, the Fiat–Shamir transcript will change to conform to the CFRG
[Fiat-Shamir Transformation specification](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/).

Polygero is described in
[Polygero: Proximity Testing From Polynomial Challenges](https://eprint.iacr.org/2026/2481)
by Matteo Frigo and abhi shelat.

| | Longfellow v1 | Longfellow v2 |
|---|---|---|
| Status | Deployed | Under development |
| Commitment protocol | Ligero | Nonrecursive Polygero |
| Combined proof implementation | `runtime::v1::zk_v1` | `runtime::v2::zk_v2` |
| mdoc application API | `mdoc::v1` | `mdoc::v2` |
| mdoc circuits | Frozen versions 5–7 | NEXT, currently version 10 |

Circuit versions have their own numbering: circuit v7 uses Longfellow v1,
while NEXT circuit v10 uses Longfellow v2.

Tests reproduce all twelve saved v1 proofs bit for bit using the same
inputs and prover randomness. V2 circuits, parameters, and proof encoding
remain subject to change. There are currently no frozen v2 mdoc circuits.

## Security bounds

The [formal v1 analysis](../formal/lfzk-v1/README.md) establishes **116-bit
Fiat–Shamir T-security** for the modeled v7 composition, under its documented
assumptions. The [formal v2 composition](../formal/lfzk-v2/README.md) bounds
extractor failure for the mathematical verifier of the MAC-free mdoc
protocol, including witness selection, layered sumcheck, the P256 adapter,
packing, joint Polygero and its single Merkle commitment. The typed theorem
allows adaptive public requests while fixing trusted circuit metadata.
The theorem uses an explicit ideal-sampler oracle and a domain-separated
Merkle random oracle. Canonical query bytes and Merkle encodings are modeled;
Rust conformance is checked by source audit. A reduction from full SHAKE byte
streams is outside the theorem. The [audit](../formal/AUDIT.md) states this
boundary. Both fields use one opening set and one active
joint-label bound, while retaining their separate rank and outside-list terms.
The ordinary-rate-1/7 profile uses `(k,s,n,t)=(349,12,2443,84)`. Its
[checked Hahn certificate](../formal/lfzk-v2/LfzkV2/Current/Parameters/Rate7.lean)
bounds each complete backend query charge below `1.999999/q`, where `q=2^128`.
[Exact numerical checks](applications/mdoc_zk/development_provider/tests/parameters.rs)
keep the implementation's geometry and complete local budgets aligned with it.
The committed binary/prime candidate caps are respectively
`21,898,356,682,154,715,916` and `451,457,457,136,012,100,305`. They give a
fingerprint-role charge of approximately `0.705/q`; efficient enumeration of
these worst-case lists is not claimed.
The [exact soundness theorem](../formal/lfzk-v2/LfzkV2/Current/IdealProofRate7.lean)
applies to every valid fixed public circuit/layout configuration of this profile.
For every pair of integers `Q >= 0` and `Q_H >= 0`, any finite classical adaptive
adversary making at most `Q` distinct transcript-oracle queries and at most
`Q_H` Merkle-oracle calls satisfies

```text
Pr[verifier accepts and the paired extractor fails to recover
   a witness satisfying the requested circuits]
  <= 2Q / 2^128
     + [4Q + 1 + Q_H(Q_H - 1)/2
        + (4886 + Q_H)(2Q_H + R + Q + 2)] / 2^256.
```

Here `R` is the number of ordinary transcript boundaries, excluding the final
seal: 492 for the two-attribute layout and 499 for the four-attribute layout.
Public requests may be chosen adaptively and proof bytes arbitrarily. The
bound permits arbitrary finite repetitions of transcript queries and includes
`Q = 0`; there is no minimum-query premise. Probability is over the ideal
oracles and the adversary's private randomness. The squared-field correction
includes chain guessing, nonzero sampling and one shared Merkle explanation.
The leading per-query charge is `2/q = 2^-127`; the positive squared-field
corrections remain explicit.
Complete V2 joint-view zero knowledge is not yet proved.

The intended transcript proof model treats one round-boundary oracle answer as
the source of both the link and the entire challenge block. Later reads,
including field rejection sampling, extend that same answer. The
[typed oracle analysis](../formal/transcript-v2/README.md) proves that feedback
pins the boundary-query order along an accepted path, except for guessed links
or an unqueried final seal. Its common exception is `ε_chain=(Q+1)/2^256` for
32-byte links. Branch exploration consumes additional queries. For ordinary
fixed-witness quadratic sumcheck with uniform field challenges the bound is
`2Q/q + ε_chain`, where `Q` bounds distinct adversarial oracle queries and `q`
is the field size. The [witness-selection analysis](../formal/witness-selection/README.md)
separately charges `choose(L,2)/q²` in the IOP and `Q*choose(L,2)/q²` in the
adaptive oracle model. Outside that event the frontend witness is unique,
removing its candidate-list multiplier. The complete composition includes
Polygero's extraction/outside-list errors and nonzero-sampling corrections.
The circuits and their public layouts are trusted. The oracle model supplies
jointly uniform typed challenge blocks and independent auxiliary randomness;
repeated queries receive the same answer. Rust's SHAKE and rejection sampling
are audited against that model.

## Performance

Complete NEXT v10 mdoc presentations, measured on 2026-11-06 with Rust 1.99.1
on a Ryzen 9 9950X, single-threaded with boost and AVX disabled.
Times are medians of 32 samples with warmups discarded; heap measurements use
separate allocation-tracking runs. The four-slot case repeats the fixture's
two disclosures.

| Attributes | Prover | Verifier | Proof bytes | Prover heap | Verifier heap |
|---|---:|---:|---:|---:|---:|
| 2 | 138.7 ms | 82.0 ms | 137,615 | 42.61 MiB | 34.70 MiB |
| 4 | 150.9 ms | 87.1 ms | 137,551 | 47.27 MiB | 37.75 MiB |

| Attributes | Raw archive bytes | Zstd archive bytes | Decoded circuit heap |
|---|---:|---:|---:|
| 2 | 632,006 | 163,286 | 1.78 MiB |
| 4 | 657,741 | 163,307 | 1.87 MiB |

Both cases use `(k,s,n,t)=(349,12,2443,84)` for the hash and signature
circuits, with ordinary code rate `k/n=1/7`. The combined hash/adapter has 20
layers; the signature has 11.
Circuit outputs join the assertion block at their own layer. Components are
ordered by decreasing depth, with original input index breaking ties, so the
carried claim weights extend in place. Fragments introduce no extra rounds.

| Circuit | Inputs | Wires excluding inputs | Terms | Sumcheck rounds |
|---|---:|---:|---:|---:|
| Hash + adapter, 2 attributes | 284,979 | 2,060,975 | 4,183,379 | 267 |
| Hash + adapter, 4 attributes | 312,383 | 2,319,775 | 4,699,279 | 274 |
| Signature, either case | 3,102 | 56,892 | 114,115 | 125 |

The binary circuit packs 128 private input bits per committed GF128 word.
Its trace-zero packing response occupies 2,064 bytes. The adapter adds a
32-byte masked prime-field claim and three bytes of masked quotient advice.
The prime-field signature side commits its remaining field inputs, one hiding
scalar and sumcheck pads. The 768 shared digest/key bits are committed only
on the binary side. Proof sizes include the 32-byte final seal and
the sampled Merkle frontier, whose size varies with the transcript.
Witness selection adds two backend cells per field and 96 bytes of responses:
32 bytes over GF128 and 64 bytes over P256. It adds no circuit wires or terms.

Peak heap is the additional live Rust heap allocation during each operation,
measured in separate runs with `bench-memory` enabled. It excludes allocations
already present at entry, allocator overhead, and stack memory; it is not
total process RSS. One MiB is 1,048,576 bytes.

Online timings include circuit decoding, native input preparation,
commitment, proof encoding or decoding, and cleanup. Inputs are already
memory-resident. Offline circuit compilation and parameter selection are
excluded.

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
Merkle trees. Shared implementations live directly under `runtime/`; protocol
implementations live under `runtime/v1/` and `runtime/v2/`. The versions have
no implementation dependency on each other. Compatibility reexports retain
the existing public v1 paths and refer to the same types and functions.

Polygero uses recursive `(Participant, Tail)` tuples ending in `()`. Each
participant keeps its field, interpolation domain, witness rows, and arithmetic
responses. Participants with the same `(k,s,n,t)` share one salted column tree
and one opening query set. All statements are bound before batching challenges,
and all responses before queries. A single field uses the same protocol through
`(participant, ())`. Field-specific rank and outside-list errors are combined
against the shared opening set without assuming independence. The zk-v2 joint
wrapper owns witness selection and
authentication for standalone proofs and mdoc. Its opaque prover and verifier
handles authenticate the fingerprint equations with the frontend statements.
The mdoc application combines its hash and signature fields in one tuple,
with one commitment and one opening. A P256-to-binary adapter connects the
signature claim to the packed digest and device-key bits. V2 uses no MACs.

Within a field, layered sumcheck combines multiple circuits with one shared
input array. Each intermediate layer has one contiguous wire array, ordered
by circuit, without padding between circuits. Only the sparse quadratic,
linear and constant terms are stored in quad fragments; local gate offsets
address the global arrays. Shorter circuits join later, aligned at their inputs.
The final shared-input claim uses one packing reduction. The mdoc binary
side combines the hash and adapter trees through this implementation.

The application circuit library builds the product-tree topology directly,
without invoking the compiler. Both proof roles instantiate its public
coefficients from the masked prime-field claim and two independent conversion
challenges. The leaves are ordinary linear expressions over the shared
Boolean inputs; intermediate nodes multiply, and two final equations assert
the rescaled prime-field claim. The application prover and verifier sequence
prime-field sumcheck, claim conversion, binary sumcheck, packing and the joint opening.

V2 binary circuits accept Boolean public and private inputs. Authenticated
packing enforces their bit representation, so the Boolean layer omits bitness
assertions on binary input wires. Internal arithmetic uses the full field;
converting an arbitrary field expression back to a Boolean still checks bitness.
Nonbinary circuits retain field-element inputs and Boolean input assertions.
Compilation rejects unused input declarations. Adapter pads in the shared
source layout are consumed by the tree. The application compiler and circuit
tests use the same input allocator and witness ordering.

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
| `runtime/algebra/`, `runtime/random/`, `runtime/merkle/`, `runtime/proto/` | Shared arithmetic, private randomness, tree primitives, and basic encodings |
| `runtime/v1/` | V1 sumcheck, Ligero, ZK orchestration, transcript, compact rows, and proof codecs |
| `runtime/v2/` | V2 sumcheck, Polygero, witness selection, packing, ZK orchestration, transcript, and proof codecs |
| `circuits/` | Reusable circuits and native witness generation |
| `applications/mdoc_zk/` | mdoc circuits, application APIs, specifications, providers, and artifacts |
| `tools/` | Rust commands for parameter auditing and specification generation |
| `src/lib.rs` | Module assembly and feature gates |
| `tests/all/dependency_tests.rs` | Dependency and source-organization checks |

Compile-time and runtime code occupy separate directories. Prover and
verifier implementations also remain separate within each protocol.

Circuit representations and codecs live in `core::proto::v1` and
`core::proto::v2`. Their readers and writers accept their own formats only.
The v1-only commitment implementation is named `runtime::v1::ligero_v1`; compact
row sampling, interpolation hints, and element codecs have explicit v1 APIs.

The circuit compiler shares its source frontend, simplification, copy rewriting,
dictionary compression, and scheduling helpers across v1 and v2 backends.
V2 represents quadratic, linear, and constant terms explicitly throughout
lowering and scheduling; each stored operand denotes a real wire. The v1 backend preserves
historical Morton ordering and circuit IDs. V2 compiles directly to
[LFC3](core/proto/LFC3.md), storing quadratic, linear, and constant terms
separately with an explicit coefficient table. It removes the reserved One wire.
V2 proof encoding uses canonical full-width elements throughout and requires
the final transcript seal. Previous V2 proof envelopes are rejected. Legacy
compact-row interfaces are explicitly named `SubfieldV1` in `subfield_v1`.
V2 binary interpolation uses the ambient field's complete 128-vector Cantor
basis, with transform preprocessing limited to the coordinates it needs.
The prover reuses one eleven-way execution split for evaluation and sumcheck;
the verifier builds the same split one layer at a time. Linear and constant
terms enter sumcheck through public corrections to the running claim.

Prime-field sampling draws only the required bytes, masks unused high bits,
and rejects out-of-range values. Its parameters are precomputed at field
construction. Existing GF128/P256 sampling byte contracts are preserved.
Packing arithmetic is opt-in: adapters provide their base field, basis,
coordinates, and relative Frobenius. Fp2 supports neither packing nor sampling.
The trace-zero packing prover and verifier return two linear equations that
Polygero authenticates against the original committed words and masks.
For GF128, trace uses two polynomial-coordinate bits and the trace-dual basis
uses the modulus's closed formula. Frobenius remains ordinary field squaring.
Auxiliary sextic arithmetic, available to tests and tooling,
defers reduction across accumulated products through the existing sumcheck
accumulator interface.

Formal proofs and parameter certificates live in [`../formal`](../formal),
including `../formal/parameters`. There are no Lean source files in the
Rust directory.

## Circuits, specifications, and providers

Applications select `mdoc::v1` or `mdoc::v2`. Each provides
`run_mdoc_prover`, `run_mdoc_verifier`, and its own `ZkSpecStruct`.

A specification identifies a circuit and fixes its commitment parameters.
The prover and verifier use the same specification and matching archive.

For v2, the hash and signature circuits share the same
`(K, N, s, T)` parameters for their joint column commitment:

| Parameter | Meaning |
|---|---|
| `K` | Polynomial dimension: K samples represent degree strictly below K |
| `N` | Number of oracle columns |
| `s` | Batching-polynomial degree bound |
| `T` | Number of opened columns and random prefix samples per row |

Generic offline parameter selection lives in `compile::polygero`. The mdoc
development provider uses one profile checked against both fields' backend
budgets. Specifications save these choices. Provers and verifiers derive the
remaining geometry deterministically; they do not tune parameters.

### Frozen circuits and NEXT

The runtime providers load registered frozen circuits without invoking
a compiler. Unknown specifications and missing artifacts are errors.

`mdoc::development_provider` handles development use. It delegates frozen
requests to the runtime providers and compiles only an explicit NEXT
request. The result contains the circuit archive and its matching v2
specification.

NEXT currently denotes circuit version 10. It is under development and is
not in the frozen registry. Saving a NEXT bundle preserves both its circuit
and its selected parameters.

Frozen artifacts and parameters are immutable. NEXT bundles store their
matching circuit archive and complete parameter specification.

Circuit archives are trusted inputs. The v2 loader supports optional
circuit-ID recomputation through `enforce_circuit_id`.

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
| `testonly` | Test fixtures and deterministic randomness; also enables both proof roles and the compiler |
| `tooling` | Offline Rust tools, including compiler and auxiliary-arithmetic dependencies |
| `bench-memory` | Benchmark allocation tracking |

The `tooling` feature is not enabled by default and does not enable proving or
verification. Auxiliary extension arithmetic is available to tests and tooling.

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

# Offline-tool tests without proof-role features.
cargo test --no-default-features --features tooling --bin zk_tool
```

Circuit synthesis and tampering tests use the native v2 compiler. Dedicated
backend tests pin v1 bytes and compare v1/v2 evaluation semantics.
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

# V2 with NEXT v10 and two attributes.
cargo bench --bench mdoc_zk_bench_next --features testonly
```

The NEXT benchmark can save a specification/archive bundle using
`MDOC_BENCH_SAVE_ARCHIVE`, or load one using `MDOC_BENCH_ARCHIVE`.
Loading a bundle preserves its saved parameters.
Set `MDOC_BENCH_ATTRIBUTES` to 2 or 4 and `MDOC_BENCH_SAMPLES` to the desired
sample count (default 8, including one discarded warmup). The test fixture has
two attributes; the four-slot workload repeats those disclosures. Subsequent
runs can load the bundle saved by the first run.

Timing and allocation tracking run separately. Add `bench-memory` for
memory measurements. It reports peak additional Rust heap, excluding
already-resident input buffers; it does not measure process RSS.
Keep allocation tracking disabled for timing comparisons.

Store benchmark archives and output outside the checkout, for example under
`/tmp/longfellow-bench/`. Raw results, logs, profiles, and caches are not committed;
the summary above records the measured code configuration.

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

## Known limitation

NEXT mdoc checks that requested namespace IDs agree with each other,
but the circuit does not authenticate those namespace IDs. Changing all
requested namespace IDs can leave a proof valid. This remains unresolved.

## License

Licensed under the Apache License, Version 2.0.
See [LICENSE](../LICENSE) for details.
