# ML-DSA cores

The optional `mldsa` feature provides public-key ML-DSA-44 and ML-DSA-65
signature cores. The encoded public key is public; the signature and 64-byte
message digest `mu` are private. SHAKE256, SampleInBall, hints and range checks
run in a binary circuit. The public-key arithmetic over `q = 8380417` is linear:
six independent, uniform prime-field row projections are pulled back through
the transposed NTT. They form one claim over F_q^6 whose terms are binary words
of the witness, and the exact mode of the
[foreign storage layer](../runtime/v2/foreign/README.md) proves it with
two GF128 product trees.

There is one packed GF128 commitment and one Polygero opening. There is no
prime-field circuit, sumcheck or commitment. The binary relation and the
adapter's fixed, challenge-free product fragment form one v2
`CircuitParticipant`; the fragment's leaves are virtual inputs defined by the
projections and the masked quotients. Each quotient is a `Word<15>` published
as a `MaskedWord<15>` over a committed `Otp<15>`, and the complete proof has a
final seal. The v2 zk wrapper performs masked witness selection before
projection challenges. The scalar wire format is `MLDSA004`; packed Keccak
uses `MLDSA005`, which also carries its packed sumcheck reduction.

SampleInBall checks the bounded 221-byte stream with a per-byte threshold
trace. Two fixed permutation networks gather accepted byte/index records and
scatter the final signed coefficients. Records contain 17 or 10 Boolean bits
and use the field's checked, injective bit encoding. Each Boolean-controlled
switch swaps the entire encoded record with one multiplication. These are
exact deterministic constraints; they introduce no new challenge or
probabilistic equality test.

An application must supply its own predicates tying `mu` to the intended
message and authorizing the public key. Native witness preparation computes
`mu` correctly, but that preparation is not a circuit constraint. The mdoc
formal security theorem does not cover this application.

`proto/` contains parameters and archive contracts; `compile/circuits/` contains
compile-time signature relations; `compile/` produces trusted circuit archives.
`runtime/` contains native witnesses, public-key projections, and separate
prover, verifier, transcript and proof-codec files. `development_provider` joins
the independent compiler and runtime implementations for offline preparation. The binary relation is archived at its natural width; the
quotient pads and the fragment's leaves lie beyond it in the shared input
array. The fragment is rebuilt deterministically from its shape, and only
setup constants (circuit IDs, layer widths, layouts) are bound before the root.

Run the benchmark from `rust/` to cover both parameter sets and all three Keccak backends.

```sh
cargo bench --offline --bench mldsa --features mldsa,testonly
```

Append `-- --list` to list the cases or `-- 44` or `-- 65` to select a parameter set.
`MLDSA_BENCH_REPEATS` controls the sample count, including one warmup.
`MLDSA_ROUNDS_PER_SLICE` optionally selects the scalar SHAKE checkpoint period
(for example 1, 2, 3 or 6); the default remains 6. Cached archives include the
complete Keccak layout in their identity. Additional benchmark options are
`MLDSA_THETA_MODE` (0–3), `MLDSA_MATERIALIZE_CHI`, `MLDSA_EXPANDED_CHI` and
`MLDSA_PACKED_CHECKPOINTS` (0 or 1). Each defaults to the production layout.
`MLDSA_SHAKE_BACKEND` accepts `scalar`, `permutations`, `rounds` or `all`.
A single selected parameter set defaults to `scalar`. The packed backends
authenticate the same sponge endpoints in one shared packed source. `rounds`
batches independent round predicates across
permutations. Source construction remains inside timed archive loading.
`MLDSA_ARCHIVES` selects an out-of-tree circuit cache; the default is
`/tmp/longfellow-mldsa`. Compilation and disk access are outside online timing.
Timings include circuit decoding, key expansion, witness preparation, the full
proof, verification, serialization and cleanup. Enable `bench-memory` separately
to measure peak live heap; allocation tracking affects timings.

The benchmark uses `(k,s,n,t) = (349,12,2443,84)`, at rate 1/7. This configuration is not a separate
formal security certificate for ML-DSA.

## Hidden encoded key

`development_provider::compile_hidden_scalar::<P>()` and `development_provider::compile_hidden_simd::<P>()`
build hidden-key ML-DSA-44 and ML-DSA-65 cores. The relation is ported from
`origin/yolo.old` at `c7c0b2f14e0596e7edebf5e273935689eaee2993`; there is no
current `yolo` branch. Both `rho` and `t1` are private. SHAKE128 expands `rho`
into the matrix, and two independently challenged multiset products check
stable rejection sampling of its first 256 accepted coefficients. The bounded
expansion supports 298 candidates per polynomial (894 SHAKE output bytes).

The native arithmetic circuit uses the sextic extension of the ML-DSA field.
It is a pure-foreign v2 `CircuitParticipant` with coordinate storage
(`zk::coordinates`): each checked coefficient is one native input whose base
coordinate is its complete bit group in the binary witness, and each sumcheck
pad stores all six coordinates as 23-bit groups after the binary relation. The
participant commits nothing. Its masked sumcheck batches every layer equation
and the input equation into one claim over F_q^6, which the coordinate map
expands into one term per stored coordinate. The exact adapter mode
authenticates that claim against the same private bits as the binary circuit,
with `Word<18>` quotients. This adds a native sumcheck while retaining one
selected GF128 commitment and one opening. The hidden-key wire format is
`HIDML005`.

The binary host is the module's own participant: it combines the relation
with the fixed adapter fragment like `CircuitParticipant`, but takes the two
permutation points as field-element public inputs and can pack its source with
the shared SIMD program. The prover and verifier drive the rounds: layout
bindings and the host commitment, the native sumcheck and its claim, the
masked quotients, the permutation points, the host sumcheck, and the opening.

The application must authorize the hidden key and bind private `mu` to its
message. This core does not include a key registry or key commitment predicate.
As with the public-key core, it is outside the mdoc formal theorem.

```rust,ignore
let circuits = longfellow_zk::mldsa::development_provider::compile_hidden_simd::<MlDsa44>()?;
let proof = longfellow_zk::mldsa::runtime::hidden::prove(
    &circuits, encoded_pk, &instance, context, rng,
)?;
longfellow_zk::mldsa::runtime::hidden::verify::<MlDsa44>(
    &circuits, context, &proof,
)?;
```

Scalar SHAKE128/256 uses the ordinary binary datapath. SIMD SHAKE uses the same
scalar sponge padding, absorption and squeeze constraints, and defers each
Keccak permutation to the 128-lane packed datapath. Its initial and final bits
occupy the same commitment cells used by the scalar constraints. The scalar
and SIMD terminal claims are fixed before a fresh batching challenge and use
one joint packing reduction. There is no second endpoint commitment.

The packed permutation commits every round state. Its theta and rho/pi
operations are public affine views, and chi uses 38,400 packed ANDs per batch.
ML-DSA-44 uses 105 permutations in one batch; ML-DSA-65 uses 189 in two. Unused
lanes carry valid zero-input permutations. This reduces computation but stores
more private state than scalar SHAKE's checkpoints, making proofs larger.

Run from `rust/` to cover all six hidden-key cases. Online timings exclude compilation.

```sh
MLDSA_BENCH_REPEATS=9 cargo bench --bench hidden_mldsa --features mldsa,testonly
```

Append `-- --list` to list the cases. For one case, append a parameter set and
backend, for example `-- 44 rounds`. The backend can be `scalar`, `permutations`
(`simd`), `rounds` or `all`.
`MLDSA_BENCH_STATS_ONLY=1` reports fixed circuit sizes without proving. Layout
and affine-view sizes are diagnostic encodings, not a supported archive loader.
The adapter fragment is rebuilt from its fixed shape during proving and
verification, as in the public-key core; only its leaves depend on the proof. Both compiled scalar circuits go
through the bounded LFC3 reader with circuit identity enforcement. Its global
limits are 67,108,864 wires, 134,217,728 terms, 64 MiB of metadata and 512 MiB
of archive bytes.

Measured on an AMD Ryzen 9 9950X, pinned to CPU 2, with Rust 1.99.1 and a native
release build. These are warm medians from eight measured samples per mode, following one warmup. Proof size varies
slightly with the Merkle queries; the table shows the measured range.

| Core | SHAKE | Prover | Verifier | Proof bytes | Fixed circuit + layout, zstd-16 |
|---|---|---:|---:|---:|---:|
| ML-DSA-44 | scalar | 634.4 ms | 309.3 ms | 93,343–94,367 | 2,390,884 B |
| ML-DSA-44 | SIMD | 197.0 ms | 110.6 ms | 268,767–269,439 | 589,216 B |
| ML-DSA-65 | scalar | 1,227.8 ms | 584.1 ms | 122,344–122,952 | 4,632,383 B |
| ML-DSA-65 | SIMD | 358.3 ms | 192.5 ms | 478,568–479,560 | 935,114 B |

| Core | SHAKE | Binary wires including inputs/output | Binary terms | Native wires | Native terms |
|---|---|---:|---:|---:|---:|
| ML-DSA-44 | scalar | 10,927,604 | 38,200,370 | 25,600 | 125,184 |
| ML-DSA-44 | SIMD | 1,796,230 | 2,562,993 | 25,600 | 125,184 |
| ML-DSA-65 | scalar | 19,306,154 | 68,202,868 | 37,120 | 175,104 |
| ML-DSA-65 | SIMD | 2,889,447 | 4,111,988 | 37,120 | 175,104 |

All binary circuits have 24 layers; the native circuits have three. The SIMD
rows additionally use 38,400 / 76,800 packed ANDs and 42,134 / 83,432 packed
source words, respectively. Online timings include witness preparation,
native and binary sumchecks, adapter construction, SIMD where selected,
the one commitment/opening, serialization and cleanup. Offline compilation
measured about 48 / 90 seconds scalar and 3.7 / 6.1 seconds SIMD.

The November 2026 audit replaced per-bit native inputs with coefficient words,
reducing the native input counts from 150,272 / 256,512 to 11,008 / 17,152. The
binary relation still enforces all bit and range checks. For `b` source bits,
centered coefficients give shifted sums below `b*q/2`; the quotient width now
uses this bound directly. The radix bound remains below the GF128 multiplicative
order, including dishonest source bits and allowed quotients. This changes
circuit identifiers; regenerate saved ML-DSA circuits, including the public-key
ML-DSA-65 artifact whose quotient advice also becomes narrower.

The shared SIMD adapter coalesces coordinate factors into fixed 128-by-128 bit
transposes, reusing them across the prover's challenge boundary and streaming
through them during verification. Binary witness preparation emits checkpoint
bits directly, avoiding temporary field vectors, and the shared prover keeps
one copy of its prepared source rather than duplicating the full SIMD witness.
These changes preserve the one-commitment protocol. Proof sizes remain dominated
by the committed Keccak round states.

Validation covers independent ML-DSA witnesses with mutations in every native
input group, scalar/SIMD SHAKE128/256 at padding and squeeze boundaries, all 128
adapter coordinates including canceled and short factors, malformed proofs and
wrong witnesses in all four hidden modes, public-key ML-DSA, and the mdoc flow.
The architecture checker now includes ML-DSA and SIMD application imports; its
fixture helper lives outside production sources, and all architecture checks pass.

A preserved pre-audit binary was rerun on the same core with the same nine-sample
settings. SIMD ML-DSA-44 improved from 239.3 / 134.0 ms to 197.0 / 110.6 ms
(prove / verify); ML-DSA-65 improved from 426.4 / 230.6 ms to 358.3 / 192.5 ms.
That is a 16–18% reduction in online time. The compressed fixed descriptions
shrank from 606,912 / 958,588 bytes to 589,216 / 935,114 bytes.

A subsequent correctness audit fixed two small-case regressions: scalar checkpoint
serialization no longer reads unused initial states, and one-/two-bit adapter
plans correctly omit the quotient-product root when no quotient advice is needed.
(Those per-proof trees were later replaced by the foreign storage layer's
fixed fragment, whose quotient words always have their full typed width.)
Regression tests reject mutations of native sumcheck messages, native pads, shared SIMD messages
and packing responses by checking algebraic residuals before any final seal.
This is implementation testing and review, not a formal soundness proof of the
ML-DSA application. Key authorization and message binding remain application predicates.

Three further audit passes rechecked constraint completeness (including all
12,288 bounded UseHint input/output combinations for ML-DSA-44/65), transcript
and commitment binding, and adversarial/boundary behavior. The proof tests now
also reject a substituted SIMD source/relation, noncanonical values in every
coordinate of a sextic field message, and proofs checked under the wrong
ML-DSA parameter set. No additional correctness defect was found in those passes.

### Foreign storage port

Both cores moved onto the v2 foreign storage layer: the exact adapter mode,
the fixed fragment with virtual leaves, and (hidden key) pure-foreign
coordinate storage. Interleaved runs against the previous per-proof-tree
implementation, pinned to one core of a shared machine, gave these warm medians
(prover / verifier, ms):

| Core | SHAKE | Before | After |
|---|---|---:|---:|
| Public ML-DSA-44 | scalar | 85.6 / 43.7 | 82.1 / 46.2 |
| Public ML-DSA-65 | scalar | 97.5 / 49.6 | 92.3 / 49.9 |
| Hidden ML-DSA-44 | SIMD | 200.8 / 108.6 | 190.8 / 93.6 |
| Hidden ML-DSA-65 | SIMD | 372.9 / 198.3 | 335.1 / 171.7 |
| Hidden ML-DSA-44 | scalar | 678.7 / 323.7 | 717.5 / 344.6 |
| Hidden ML-DSA-65 | scalar | 1,250.9 / 582.2 | 1,325.0 / 610.1 |

The public-key verifier and the scalar hidden-key prover are slower. In the
public-key benchmark, which decodes the circuit inside each timed call, v2's
mandatory circuit-ID check adds about 6 ms per decode while proving and
verifying themselves got faster. The fragment's virtual leaves widen the
shared input array, which crosses a power of two for ML-DSA-44 (public key)
and for both scalar hidden-key circuits.
