# Formal verification

**The modeled v7 Longfellow verifier using Ligero V1 has 115-bit T-security.** For the
signature and SHA circuits with one through four attributes on one
Fiat–Shamir transcript, the certified soundness error is at most
`(1 + tA + N) / 2^115`, where `tA` and `N` are the Merkle- and
transcript-oracle query budgets. This is the conditional two-circuit theorem
[`v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac`](lfzk/Lfzk/CompiledZkProfileSepMac.lean);
its premises and deployment boundary are stated in the
[Longfellow README](lfzk/README.md).

The current hash-side core exceeds `2^-116` in every v7 profile, as certified
by [`hash_core_exceeds_116`](lfzk/Lfzk/SoundnessAudit.lean); these rows cannot
give a 116-bit combined bound by changing only the final composition.

Ligero V1 is the shipped component protocol. V2 and V3 are alternatives under
development; their component-level analyses are documented separately in the
[Ligero README](ligero/README.md).

The Ligero development proves:

- Reed–Solomon code distance, affine triple-counting and selected-MCA bounds,
  and JB agreement with checked η³ threshold parameters.
- Delsarte's LP bound using Hahn kernels for uniform intersection families,
  with Johnson as the degree-one case. It certifies the V1 unchecked-mask list
  below the Johnson threshold.
- Response-assisted scalar IOP extraction for Ligero V1, V2, and V3, together
  with response-uniform envelopes and false-statement soundness.
- Merkle prefix binding and typed Fiat–Shamir query bookkeeping.
- Exact IOP certificates for v7/v8 signature and hash geometries across all
  three variants, and local challenge/query count certificates for the hash
  geometries and V1 signatures.

See the [Ligero README](ligero/README.md) for component theorem names and
certificates. This package also contains the EC/ECDSA circuit development and
sumcheck modules.

The [recursive Polygero development](polygero/README.md) proves witness
extraction for the transmitted recursive public-coin verifier, with failure
bound `1 − ∏ᵢ(1 − εᵢ)` from certified local errors. False-statement soundness
is derived from extraction validity and the same failure bound. It reuses
the Ligero code and tableau infrastructure.

From this directory:

```sh
lake build
```

The package uses Lean 4.31.0 and the compatible Mathlib checkout at
`../../mathlib4`, relative to `formal/`.
