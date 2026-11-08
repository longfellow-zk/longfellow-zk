# Trace-pairing dual packing

`DualPacking` proves completeness and a `1 / |F|` false-claim bound for the
packing adapter over any finite extension `F / K`. The committed field words
have canonical `K`-coordinates in a supplied basis. For `K = ZMod 2`, every
coordinate is a bit; no separate bitness constraint is needed.

From `formal/`:

```sh
lake build DualPacking
lake env lean dual-packing/audit.lean
lake env lean scripts/Audit.lean
```

The library is included in the default build, with warnings treated as errors.
The endpoint audit prints its theorem dependencies; the existing global audit
also checks every imported `DualPacking` declaration, including private helpers,
and permits only `propext`, `Classical.choice`, and `Quot.sound` for this library.

## Protocol

Let `sigma(x) = x^|K|`, and let `beta` and `alpha` be trace-dual bases. The
coefficient conversion turns a query on the coordinates of packed words into
one trace check per output coordinate. The honest first response is

```text
U[k] = B[k] - alpha[k]*target + sigma(t[k]) - t[k].
```

The verifier checks `trace(U[k]) = 0` before sampling independent uniform
`delta[k]` in `F`. The prover then responds with
`A = r + sum delta[k]*t[k]`. Two equations, linear in the committed words and
mask cells, authenticate this response. The dependent mask is expanded into
coefficients on the original free mask cells. This trace-zero protocol uses
`m+1` adapter cells and `m+1` transmitted field elements for an extension of
degree `m`. The Rust degree-one path instead checks the original linear
equation directly, with no packing masks, messages, or challenges.

The Rust reduction is internal to ZK. Its source equation is derived from
preceding sumcheck messages and oracle answers on the same transcript. It
binds arbitrary caller-supplied statement bytes, the packing profile and
public cell counts; it does not absorb the derived coefficients or RHS.
The [current composition](../lfzk-v2/README.md#current-mac-free-protocol)
proves that the source is fixed before the packing answer and is the source
recovered at the later backend. U and A retain their existing round ordering.

The main verifier is `Instance.nativeLinearVerify`. It does not check
`b = sigma(r)`: arbitrary committed `b` contributes a fixed affine offset,
which preserves the `1 / |F|` bound. Honest initialization uses that equality
for completeness. `nativeVerify` adds the optional consistency check and is
retained for comparison and adversarial regression cases.

## Runtime correspondence

These are algebraic component proofs, not a source-level verification of the
[Rust adapter](../../rust/runtime/v2/dual-packing/src/lib.rs). Names below are in
`DualPacking.ArtinSchreier` unless prefixed with `DualPacking`.

| Rust operation | Lean theorem or definition |
|---|---|
| Pack and recover input coordinates | [`DualPacking.reconstruct`, `DualPacking.digit_pack`, `DualPacking.canonical_bit`](DualPacking/Coordinates.lean) |
| Precompute the trace-dual basis | [`DualPacking.traceDual_eq_gramDual`, `DualPacking.traceDual_eq_of_pairings`, `DualPacking.powerBasis_traceDual`](DualPacking/DualBasis.lean) |
| Evaluate trace and Frobenius as base-field linear maps | [`trace_coordinates`, `frobenius_coordinates`](DualPacking/ArtinSchreierAlgebra.lean) |
| Convert public query coefficients and compute `B` | [`coefficient`, `trace_forms`, `coefficient_eq_dualPack`](DualPacking/ArtinSchreierAlgebra.lean) |
| Form `U` and the scalar response | [`Instance.honestU`, `Instance.honestA`, `Instance.linear_completeness`](DualPacking/ArtinSchreier.lean) |
| Eliminate the dependent mask | [`Instance.contract_mask`](DualPacking/ArtinSchreierBackend.lean) |
| Emit the two linear constraints, including an affine target | [`Instance.nativeOne`, `Instance.nativeTwo`, `Instance.nativeLinearVerify_affine`](DualPacking/ArtinSchreierBackend.lean) |
| Bound false-claim acceptance with arbitrary committed cells | [`Instance.linear_native_soundness_probability`](DualPacking/ArtinSchreierBackend.lean) |
| Retain backend failure as a separate event | [`Instance.linear_backend_composition_card`](DualPacking/ArtinSchreierBackend.lean) |

`linear_soundness_binary128` gives `1 / 2^128` from a binary basis of size 128.
`linear_soundness_prime_degree_six` gives `1 / p^6` over `ZMod p` from a basis
of size six. The field sizes follow from the bases, rather than from separate
cardinality assumptions. [BinarySpecialization](DualPacking/BinarySpecialization.lean)
identifies the binary equations, and [FiniteFieldCases](DualPacking/FiniteFieldCases.lean)
checks honest and malicious examples in an actual odd-characteristic extension.

## Assumptions and boundary

The committed words, mask cells, target and entire first response are fixed
before the independent vector challenge. The scalar response may depend on the
whole challenge. The theorem assumes exact fields, an actual basis, the
relative Frobenius, and exact authentication of the two native equations.

The fixed-commitment counting theorem is composed with the native affine
frontend and Polygero in [`LfzkV2.Packed`](../lfzk-v2/README.md). The staged
[Fiat–Shamir theorem](../lfzk-v2/LfzkV2/Packed/FiatShamir.lean) keeps the
independent packing challenge between `U` and the scalar response `A`.
[CompiledFS](../lfzk-v2/LfzkV2/Packed/CompiledFS.lean) constructs both actual
row systems and proves their transfer to the frontend; its direct constructor
has no packing challenge and zero packing budget.

[Inputs](../lfzk-v2/LfzkV2/Packed/Inputs.lean) embeds active input positions
into packed coordinates, with zero coefficients on the unused tail of the
last word. [ProfiledSide](../lfzk-v2/LfzkV2/Packed/ProfiledSide.lean) chooses
the certified candidate bounds before constructing those compiler instances.
The authenticated endpoint
[`LfzkV2.Packed.RawRuntimeExtraction.extraction_117`](../lfzk-v2/LfzkV2/Packed/RawRuntimeExtraction.lean)
proves `(1+N+tA)/2^117` for the native quadratic-backend model at commit
`fcf8a3a`, under the circuit/layout, sampler, MAC-row and Merkle-codec premises
in the [Longfellow V2 scope statement](../lfzk-v2/README.md).

Rust field arithmetic, concrete array layouts, serialization and transcript
encoding remain implementation correspondence obligations. Joint zero
knowledge is not established by this development. The later linear-terminal
backend is outside this formal checkpoint.
