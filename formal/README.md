# Formal verification

**The modeled linear-terminal Longfellow V2 verifier at commit `21cb029`
has a 116-bit work-normalized extraction bound.** The native affine frontend,
binary-input packing, linear-only Polygero backend, two-field MAC, and both
Merkle openings share one adaptive Fiat–Shamir transcript.
[`LfzkV2.Linear.Runtime.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Linear/Runtime/RawRuntimeExtraction.lean)
proves `Pr[accept ∧ paired extraction fails] ≤ (1 + N + tA) / 2^116` for all
transcript-query budgets `N` and Merkle-query budgets `tA`. The exact finite
bound is also proved. Circuit/layout, sampler, MAC-row and codec premises
remain explicit; see the [audit and implementation boundary](AUDIT.md).

The prior product-checked snapshot `fcf8a3a` retains its separate
[`Packed.RawRuntimeExtraction.extraction_117`](lfzk-v2/LfzkV2/Packed/RawRuntimeExtraction.lean)
certificate without changes. Its constants do not describe the randomized
linear terminal.

The earlier v7 verifier using Ligero V1 retains its 116-bit extraction and
false-statement soundness bounds for signature and SHA circuits with one
through four attributes. Its flat zero-query and graded positive-query
proofs are checked by [`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean).
The [Longfellow V1 README](lfzk-v1/README.md) states their premises.

Version 7 uses Ligero V1; version 8 uses Polygero. The
[Ligero README](ligero/README.md) documents the component analysis.

The default `lake build` includes all 16 retained Hahn/Delsarte certificate
families: five runtime Polygero profiles, six v7 Ligero mask certificates, and
five Polygero benchmark certificates. It also checks their numerical endpoints
and an [axiom audit](parameters/hahn/RuntimeHahn/APITest.lean). The Hahn identities
use exact integer checks and a proved polynomial interpolation theorem; no
native-evaluation axiom is needed for the certificates.

Run `lake build` or `scripts/build.sh` from this directory to build the default
targets with Lean and Lake's default concurrency. The script also accepts individual Lake targets.

The Ligero development proves:

- Reed–Solomon code distance, affine triple-counting and selected-MCA bounds,
  and JB agreement with checked η³ threshold parameters.
- Delsarte's LP bound using Hahn kernels for uniform intersection families,
  with Johnson as the degree-one case. It certifies the V1 unchecked-mask list
  below the Johnson threshold.
- Response-assisted scalar IOP extraction for Ligero V1, together
  with response-uniform envelopes and false-statement soundness.
- Merkle prefix binding and typed Fiat–Shamir query bookkeeping.
- Exact IOP certificates for v7 signature and hash geometries, and local
  challenge/query count certificates for the hash
  geometries and V1 signatures.

See the [Ligero README](ligero/README.md) for component theorem names and
certificates. This package also contains the EC/ECDSA circuit development and
two sumcheck libraries:

- [Sumcheck V1](sumcheck-v1/SumcheckV1/README.md), imported as `SumcheckV1`,
  contains the legacy round, chain, and challenge-tape proofs used by `LfzkV1`.
- [Sumcheck V2](sumcheck-v2/README.md), imported as `SumcheckV2`, proves the
  projective round update, honest table folding, single-hand layer reduction,
  masked constraint equations, and challenge-tape bounds. These are component
  theorems; the `LfzkV1` security certificates above still use V1.

[Longfellow V2](lfzk-v2/README.md), imported as `LfzkV2`, connects the native
affine circuit, linear and quadratic assertions, honest prover, and actual
compiled rows. Its staged replay fixes the packing response `U` before an
independent vector challenge and the scalar response `A` afterward. Packing
and layer checks read the same authenticated cells. The degree-one signature
path keeps its original source equation and has no packing challenge or cost.

The packed hash and direct signature sides both use geometry
`(n,k,s,t) = (2912,416,15,86)`, with certified candidate bounds 25 and 33.
Before Merkle costs, the adaptive bound is
`925*N/2^128 + 19303/2^128 + 21661/2^255`; raw verification adds one transcript
lookup. The authenticated extractor returns satisfying witnesses with equal
common messages. Exact startup and small-Merkle bounds yield the all-budget
116-bit endpoint above. This conservative numerical certificate includes
`2/(|F|-1)` per layer, with 20 hash layers and 21 signature layers; the
field-normalized theorem retains the exact nonzero denominator. The older
product-checked and unpacked compositions remain separate models.

Backend response/opening simulation and affine-MAC privacy remain component
results: complete joint frontend/backend/Merkle zero knowledge is not proved.
API and axiom checks are in the default build. Rust arithmetic, concrete
layouts, parsing and byte-level transcript correspondence remain implementation
obligations.

The [recursive Polygero development](polygero/README.md) proves witness
extraction for the transmitted recursive public-coin verifier, with failure
bound `1 − ∏ᵢ(1 − εᵢ)` from certified local errors. False-statement soundness
is derived from extraction validity and the same failure bound. It reuses
the Ligero code and tableau infrastructure.

[Dual packing](dual-packing/README.md), imported as `DualPacking`, proves
trace-pairing coordinate recovery and the two native linear constraints for
packing over arbitrary finite field extensions. Its fixed-commitment
false-claim bound is `1 / |F|`, including arbitrary committed mask cells.
The library and its binary and odd-characteristic regression cases are in
the default build. The native compiler and staged Fiat–Shamir composition in
`LfzkV2.Linear.Runtime` lift this fixed-claim bound to the authenticated endpoint above.

From this directory:

```sh
lake build
```

The package uses Lean 4.31.0 and the compatible Mathlib checkout at
`../../mathlib4`, relative to `formal/`.
