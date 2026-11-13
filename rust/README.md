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
Its legacy index and opening samplers live on the v1 transcript, including
the original extra-bit rejection behavior at power-of-two bounds. Shared
`RandomEngine` contains no index sampler; its v1 extension is limited to
legacy subfield sampling.
V2 uses SHA-256 strands with explicit message and challenge phases. A root
has id zero and no parents. Each round consumes its absorbing strand and returns
a PRF and a fresh one-parent continuation with id `parent.id + 1`.
The node hash binds `u32(STRAND) || u64(id) || u32(parent_count) || parent`
before the message, and PRF blocks hash
`u32(PRF) || u64(id) || digest || u64(counter)`. Integers are little endian;
strand ids and PRF counters are checked against overflow. Distinct node and
PRF positions therefore have distinct inputs even if digests collide. PRF
reads do not affect the continuation. Separate executions can replay the same
inputs. Round labels are protocol-format constants owned by
`v2::proto`; the generic transcript binds their numeric tags. Finalized states
stay private, and PRF block zero supplies the first challenge bytes.
Index sampling uses the minimum bit width for values below its bound,
so power-of-two bounds require no rejection and a singleton consumes no bytes.
Sampling without replacement updates that bound after each selected index.
Complete proofs end with a 32-byte final seal: a PRF challenge computed from
the strand binding the complete canonical proof body, including terminal
authentication data. Both parties compute it, and verification checks the
value stored in the proof.

The v2 Merkle codec separately tags leaves and internal nodes. Leaves bind
their column index; internal nodes bind their heap index, with root 1 and
children `2*i` and `2*i + 1`. The traversal supplies these indices, which are
encoded as little-endian u64 values and require no proof bytes. Distinct tree
positions have distinct hash inputs even when their child digests coincide.

V2 callers receive separate writing and reading capabilities. `begin_squeeze` consumes
the writer; closing the reader returns the round-completion token. Public
cloning, resetting, raw-state access, and use as private prover randomness are
unavailable. Complete-proof encoders own finalization, and decoding returns
immutable unverified data. Only complete verification returns `VerifiedProof`
evidence after checking the seal.
Commitment sessions own the transcript through authentication. Frontends borrow
a restricted `TranscriptRef` that cannot replace or finalize that session;
successful authentication releases it for the complete-proof seal.

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
| Combined proof implementation | `runtime::v1::zk` | `runtime::v2::zk` |
| mdoc application API | `mdoc::v1` | `mdoc::v2` |
| mdoc circuits | Frozen versions 5–7 | NEXT, currently version 12 |

Circuit versions have their own numbering: circuit v7 uses Longfellow v1,
while NEXT circuit v12 uses Longfellow v2.

Tests reproduce all twelve saved v1 proofs bit for bit using the same
inputs and prover randomness. V2 circuits, parameters, and proof encoding
remain subject to change. There are currently no frozen v2 mdoc circuits.

## Security bounds

The [formal v1 analysis](../formal/lfzk-v1/README.md) establishes 116-bit
Fiat–Shamir T-security for its modeled v7 composition. The current v2
numbered-strand model has a checked one-SHA extraction theorem for adaptive
public requests and arbitrary complete serialized proofs. It includes witness
selection, layered sumcheck, the cross-field adapter, packing, joint Polygero,
its shared indexed Merkle commitment and the final seal.

Let $P_{\mathrm{fail}}$ be the probability that the verifier accepts and the
paired extractor fails to recover a witness satisfying the requested circuits.
For every integer $0\le Q<2^{127}$, any finite classical adaptive adversary
making at most $Q$ distinct original SHA queries satisfies

$$
\begin{aligned}
P_{\mathrm{fail}}(Q)
&\le \frac{cQ}{q}
 + \left(1-\frac{c(q-1)}{2q}\right)
   \left[1-\left(1-\frac{2}{q-1}\right)^Q\right] \\
&\quad + \frac{\binom Q2+r+15}{q^2},
\qquad q=2^{128}.
\end{aligned}
$$

Here $c=1.0000012312149082441647508747\ldots$ is the exact parameter-dependent
Polygero coefficient defined in the [formal README](../formal/README.md#v2-extraction-soundness).
The full failure probability is **strictly less than 0.97** for $Q<2^{127}$.
The leading shared-budget bound also holds for every $Q\ge0$:

$$
P_{\mathrm{fail}}(Q)\le
\frac{2Q}{2^{128}-1}+\frac{\binom Q2+r+15}{2^{256}}.
$$

A convenient approximation for the mdoc circuit, valid for every $Q\ge0$, is

$$
P_{\mathrm{fail}}(Q)\le Q\,2^{-127}+Q^2\,2^{-257}+2^{-246}.
$$

The supported one-/two-/three-/four-attribute circuits have 488/492/497/500 rounds.

Here `r` counts ordinary transcript boundaries, one per `begin_squeeze()`.
The final seal's node hash and PRF hash are accounted for separately.
The same SHA function supplies public setup hashes,
adversarial answers, numbered strand nodes, indexed PRF blocks and indexed
Merkle authentication. Repeated queries reuse answers. The query budget
counts the original adversarial program. Verifier replay appears in the
explicit correction.

The ordinary rate-1/7 profile uses `(k,s,n,t)=(349,12,2443,84)`. Its
[checked Hahn certificate](../formal/lfzk-v2/LfzkV2/Current/Parameters/Rate7.lean)
gives the exact joint backend allowance `c/q`, including both fields.
[Exact numerical checks](applications/mdoc_zk/development_provider/tests/parameters.rs)
align the implementation geometry and local budgets. The committed
binary/prime candidate caps are respectively
`21,898,356,682,154,715,916` and `451,457,457,136,012,100,305`.
They give a fingerprint-role charge of approximately `0.705/q`.

The [exact endpoint](../formal/lfzk-v2/LfzkV2/Current/Mdoc/OracleSoundness.lean)
constructs metadata, advice decoding, layouts and frontend plans from trusted
circuit topology and canonical field representations. It derives ordered
query recovery, agreement on opened columns, failure coverage and one shared
query budget. The public setup and complete verifier use the same oracle.
The [audit](../formal/AUDIT.md) records the proof path and implementation scope.

The cryptographic assumptions are a classical ideal SHA oracle and the
stated joint successful-sampling law for the physical role readers, including
nonzero scalars and openings without replacement. Failed samplers reject;
proving that the concrete Rust rejection loops satisfy the joint sampling law
remains a separate implementation obligation.
The field codecs, circuit semantics and static public resource bounds are
trusted model inputs. Rust correspondence is established through source audit
and tests. Machine-level refinement and extractor running-time bounds remain
open. The exact `q-1` denominator retains the nonzero-sampling correction.

The [complete numbered-strand zero-knowledge theorem](../formal/lfzk-v2/README.md#current-numbered-strand-zero-knowledge)
gives a witness-free simulator with ideal-model distinguishing error at most
`(Qpre+Qpost)/2^256`. Public setup and both observer traces use the same SHA
oracle as the complete proof. `Qpre` and `Qpost` count raw calls before and
after the proof, including repetitions and verification calls when the
verifier is observed. The actual verifier's acceptance probabilities obey
the same comparison, including rejection and simulator-abort outcomes.

The theorem assumes independent uniform private coins, trusted
fields/codecs/circuits and layout bounds, and a fixed witness policy valid
at contexts reached using setup derived from the same oracle. Ordinary hash
witness satisfaction and static hash-circuit noninterference are separate
premises, alongside the basis/generator checks. V2 uses a
32-byte nonce per committed column, with one `NONCE_LEN` constant shared by
sampling, codecs and size estimates. At `Qpre+Qpost <= 2^128`, the ideal-model
error is at most `2^-128`. The 84 opened columns carry 2688 nonce bytes;
SHA-256 digests are also 32 bytes.

At `2^128` queries, the assumption that SHA-256 behaves as an ideal oracle
becomes itself questionable. The bound above should therefore not be interpreted
as 128 bits of hiding for the concrete implementation. The parameters put
the bottleneck in SHA-256 itself, rather than the rest of the protocol.

The [transcript analysis](../formal/transcript-v2/README.md) proves the logical
query-accounting interface used by the raw SHA coupling. The soundness endpoint accounts
for numbered SHA strand nodes and counter-indexed PRF queries directly.
The [witness-selection analysis](../formal/witness-selection/README.md)
charges `Q*choose(L,2)/q²` for candidate selection. The full composition
retains Polygero's extraction/outside-list errors and nonzero-sampling terms.

## Performance

Complete NEXT v12 mdoc presentations, measured on 2026-11-10 with Rust 1.99.1
on a Ryzen 9 9950X, single-threaded with boost disabled and the native CPU target.
Times are medians of seven samples after one warmup;
heap measurements use separate allocation-tracking runs. The four-slot case
repeats the fixture's two disclosures.

| Attributes | Prover | Verifier | Proof bytes | Prover heap | Verifier heap |
|---|---:|---:|---:|---:|---:|
| 2 | 140.2 ms | 75.5 ms | 138,575 | 43.06 MiB | 34.73 MiB |
| 4 | 145.0 ms | 77.0 ms | 138,735 | 47.65 MiB | 37.78 MiB |

| Attributes | Raw archive bytes | Zstd archive bytes | Decoded circuit heap |
|---|---:|---:|---:|
| 2 | 654,541 | 160,968 | 1.74 MiB |
| 4 | 679,625 | 162,552 | 1.83 MiB |

Both cases use `(k,s,n,t)=(349,12,2443,84)` for the hash and signature
circuits, with ordinary code rate `k/n=1/7`. The combined hash/adapter has 20
layers; the signature has 11.
Circuit outputs join the assertion block at their own layer. Components are
ordered by decreasing depth, with original input index breaking ties, so the
carried claim weights extend in place. Fragments introduce no extra rounds.

| Circuit | Inputs | Wires excluding inputs | Terms | Sumcheck rounds |
|---|---:|---:|---:|---:|
| Hash application, 2 attributes | 285,469 | 2,076,110 | 4,250,351 | 267 |
| Hash application, 4 attributes | 312,873 | 2,335,336 | 4,766,971 | 275 |
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

The signed-MSO bounds and offset-ordering checks change the hash circuit ID.
Regenerate V2 circuit archives and their matching specifications when upgrading;
existing archives retain their original circuit checks.

## Architecture

The ZK implementation coordinates commitment and sumcheck. Sumcheck reduces
circuit satisfaction to constraints on committed witnesses and masking
values. A runtime constraint compiler translates those results into the
equations checked by Ligero or Polygero.

The runtime constraint compiler is separate from the offline circuit
compiler. Proving and verification do not require the `compiler` feature.

V1 and v2 implementations occupy separate directories and have their own
application types, specifications, transcripts, and proof codecs. They share
arithmetic, interpolation and private randomness. Each version owns its Merkle
tree, hashing, nonce/proof types and wire codecs. Shared implementations live
directly under `runtime/`; protocol
implementations live under `runtime/v1/` and `runtime/v2/`. The versions have
no implementation dependency on each other. Compatibility reexports retain
the existing public v1 paths and refer to the same types and functions.
In particular, `runtime::merkle` and `runtime::proto` are aliases to v1.
V2 uses distinct digest types, internal Merkle operations and canonical field
decoding; its nonce types and authentication envelope remain internal.

Polygero uses recursive `(Participant, Tail)` tuples ending in `()`. Each
participant keeps its field, interpolation domain, witness rows, and arithmetic
responses. Attaching a participant validates both its domain identity and the
interpolation capacity of the supplied backend. The domain supplies the
arithmetic field, keeping runtime moduli consistent with interpolation.
Participants with the same
`(k,s,n,t)` share one salted column tree
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

The hash circuit reads the credential inputs, including the 768 bits shared
with the adapter. Its final 256 mask bits and 20 quotient-pad bits are reserved
after compilation and must be unread by every hash gate and assertion. Tests
exhaustively check this boundary in all four compiled circuit shapes, with no
runtime scan. Adapter challenges and masked advice enter only the separately
generated product-tree circuit.
The adapter authenticates the mask modulo the P256 prime, so its binary copy
needs no range check. The honest prover still samples a uniform field mask
and writes its canonical bits; packing supplies their Boolean interpretation.

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

The hash circuit checks that every selected field ends within the unpadded
signed message. The docType check requires the exact CBOR text type, encoded
length and value, with explicit suppression retained. Signature1 and tag-24
wrapper lengths are checked against the signed preimage. IssuerSignedItem
slots require unsigned digest IDs and byte-string salts, and public slice
lengths are bounded by their arrays. Carry-save arithmetic lives in the
arithmetic module and is exposed through bitvec; the existing sum-checking
primitive checks the wrapper lengths. These checks add no circuit inputs.

Frontend `reduce` methods return equations awaiting authentication; complete
`verify` methods authenticate them and check the final seal. Revealed-pad
sumcheck diagnostics are confined to tests.

Sumcheck does not depend on Ligero, Polygero, or the combined ZK
implementation. The top-level dependency checker enforces these boundaries,
including code behind inactive feature gates.

V2 runtime circuits are read-only at the type level, including generated
adapter instances. `RawCircuitBuilder` owns mutable construction data;
`build()` transfers it into a `RawCircuit` without allocating or scanning.
Finalized `Circuit` and `RawCircuit` expose only immutable field access, so
their constants, gate streams, cached assertion counts, and identity cannot
be mutated. Editing requires consuming the circuit back into a builder and
constructing a new circuit. Trusted constructors remain responsible for
consistent metadata; proving and verification add no validation work.

### Source layout

This is one Cargo crate, `longfellow-zk`. The directories organize modules;
they are not separate crates.

| Directory | Contents |
|---|---|
| `core/` | Basic algebra interfaces, circuit representations, and circuit serialization |
| `compile/` | Symbolic arithmetic, circuit compilation, and offline parameter selection |
| `runtime/algebra/`, `runtime/random/` | Shared arithmetic, interpolation and private randomness |
| `runtime/v1/` | V1 sumcheck, Ligero, ZK orchestration, transcript, compact rows, Merkle tree and proof codecs |
| `runtime/v2/` | V2 sumcheck, Polygero, witness selection, packing, ZK orchestration, transcript, Merkle tree and proof codecs |
| `circuits/` | Reusable circuits and native witness generation |
| `applications/mdoc_zk/` | mdoc circuits, application APIs, specifications, providers, and artifacts |
| `tools/` | Rust commands for parameter auditing and specification generation |
| `src/lib.rs` | Module assembly and feature gates |
| `tests/all/dependency_tests.rs` | Dependency and source-organization checks |

Compile-time and runtime code occupy separate directories. Prover and
verifier implementations also remain separate within each protocol.

Circuit representations and codecs live in `core::proto::v1` and
`core::proto::v2`. Their readers and writers accept their own formats only.
The v1-only commitment implementation is named `runtime::v1::ligero`; compact
row sampling, interpolation hints, and element codecs have explicit v1 APIs.

The circuit compiler shares its source frontend, simplification, copy rewriting,
dictionary compression, and scheduling helpers across v1 and v2 backends.
V2 represents quadratic, linear, and constant terms explicitly throughout
lowering and scheduling; each stored operand denotes a real wire. The v1 backend preserves
historical Morton ordering and circuit IDs. V2 compiles directly to
[LFC3](core/proto/LFC3.md), storing quadratic, linear, and constant terms
separately with an explicit coefficient table. Its `DIR2` directory declares
all array sizes before the payload; segment contents use contiguous storage.
Global limits bound layers, total wires, term data, and segment/token metadata.
It removes the reserved One wire.
V2 proof decoding checks canonical full-width elements through one shared
reader and requires the final transcript seal. Previous V2 proof envelopes are
rejected. Legacy compact-row interfaces are explicitly named `SubfieldV1` in `runtime::v1::subfield`.
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
Packing is internal to ZK. Its prover and verifier return two linear equations
that Polygero authenticates against the original committed words and masks.
Its transcript binds a caller-supplied statement, packing profile and cell
counts. The coefficients and affine RHS are derived from the preceding
sumcheck on the same transcript and are not absorbed again. The U vector
precedes the packing challenge; the scalar A precedes backend challenges.
Degree-one packing performs no transcript operations.
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

NEXT currently denotes circuit version 12. It is under development and is
not in the frozen registry. Saving a NEXT bundle preserves both its circuit
and its selected parameters.

Frozen artifacts and parameters are immutable. NEXT bundles store their
matching circuit archive and complete parameter specification.

Circuit specifications are trusted configuration. Every v2 circuit load
recomputes its SHA-256 ID from the stored segmented representation and checks
it against the payload and archive identifiers. There is no enforcement flag.
Compilation returns an identity-free `RawCircuit`; segmentation finalizes its
representation and computes its ID. Changing segmentation or coefficient-table
order changes the ID. LFC3 revision `DIR2` uses this convention; older NEXT
bundles must be regenerated.

To measure circuit-ID computation and checked decoding on the largest mdoc
circuit, run `cargo bench --bench circuit_id`. Set
`CIRCUIT_ID_BENCH_ATTRIBUTES=1,2,3,4` to measure all attribute counts. Compilation
is outside timing; the benchmark reports median and 95th-percentile times.

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
| `arm-neon` | ARMv7 NEON field arithmetic; also requires the compiler's NEON target flag |
| `bench-memory` | Benchmark allocation tracking |

The `tooling` feature is not enabled by default and does not enable proving or
verification. Auxiliary extension arithmetic is available to tests and tooling.

Feature gates are placed high in the module tree. The `cfg_compiler!`,
`cfg_prover!`, `cfg_verifier!`, `cfg_prover_or_compiler!`, and
`cfg_testonly!` macros in `src/lib.rs` group conditional declarations.

## Building and testing

Run commands from this directory. Normal builds use stable Rust.
Repository formatting uses nightly Rust. Native CPU flags are scoped to the
local x86-64 Linux target; other cross targets do not inherit the host CPU.
The local native build is intended for its build machine. Distributed binaries
must select their deployment CPU features explicitly.

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

ARMv7 Linux builds use ARM integer arithmetic and scalar binary-field arithmetic
by default. `cargo build-armv7-neon --release` selects the NEON field backend and
sets the required compiler flag; the resulting binary requires a NEON-capable
CPU. Selection happens at build time. `force-generic-arch` overrides either
backend. Cross builds require `arm-linux-gnueabihf-gcc`.
`cargo test-armv7-neon --features testonly` runs the NEON tests on ARM hardware
or through a locally configured Cargo runner. Rust emits an unstable-feature
warning for the `+neon` compiler flag; the backend uses stable inline assembly.

## Benchmarks

```sh
# V1 with circuit v7 and two attributes, using an LFA2 archive.
MDOC_BENCH_ATTRIBUTES=2 \
  cargo bench --bench mdoc_zk_bench_v1 --features testonly -- lfa2

# V2 with NEXT v12 and two attributes.
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

The catalog includes the production joint mdoc profile `(349, 12, 2443, 84)`.
Its geometry is shared with the development provider through
`MDOC_JOINT_PROFILE`. The exact checker checks its shared two-field parent,
opening and fingerprint charges separately from the universal tuning profiles.
`certify-hahn` checks the three mdoc Hahn bounds and binds the manifest's
cutoffs and list caps to `MdocJointProfile.profile`. It checks every staged
module in dependency order, using two workers by default, two Lean threads,
a 4,096 MiB limit and a 60-second deadline per module. Source-identical cache
reuse also requires reusable staged dependencies.

After certification, select that profile for the Lean cross-check with
`check-profiles --protocol polygero --check-lean ../formal --profile 349,12,2443,84`.

Parameter certificates establish mathematical bounds under their stated
assumptions; they do not certify the complete Rust implementation.

The tools are written in Rust. Python is not required.

## Known limitations

NEXT mdoc takes one global namespace from the requested attributes. The
namespace must be nonempty UTF-8 text of at most 64 bytes, and all requests
must agree. Its bytes and length are public circuit inputs. The circuit checks
the exact CBOR text at a private offset in the signed MSO, including the complete
read range. Honest witness construction selects that namespace once and then
looks up attributes by name within it. Namespace checking cannot be suppressed.

Private field offsets are checked for matching bytes and complete read bounds,
but the circuit does not establish their CBOR ancestry. It does not prove that
selected digests belong to the requested namespace map. Namespace occurrence
alone is not a proof of that membership.

Validity comparisons select the fourteen `YYYYMMDDhhmmss` digits from the
supported 20-byte UTC representation. V2 entry points check ASCII digits and
`YYYY-MM-DD[Tt]hh:mm:ss[Zz]` syntax, and require a nonempty document type.
The native prover checks the signed document type and inclusive validity window
before witness construction. Calendar validity remains an assumption of the
circuit; neither the syntax check nor the circuit validates calendar ranges.

V2 validates device-key COSE type/curve metadata, exact 32-byte canonical
coordinates and curve membership before fixed-width conversion. Requested
attribute values are checked before constructing their SHA witnesses. These
host checks give earlier rejection and do not replace circuit constraints.

Native witness preparation and generic field inversion are variable time.
The formal zero-knowledge theorem concerns protocol and oracle observations;
it does not establish protection against local timing or cache observation.

The signature circuit retains its affine precomputation layout. Exceptional
signatures whose precomputed sums are points at infinity remain unsupported;
v2 witness construction returns `WitnessCreationFailure` instead of panicking.

## License

Licensed under the Apache License, Version 2.0.
See [LICENSE](../LICENSE) for details.
