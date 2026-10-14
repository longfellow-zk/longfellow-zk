# Formal verification

**Ligero V1 is the shipped protocol. V2 and V3 are alternative protocols
under development.**

The certified v7/v8 bounds are shown below, in bits. Let `L = log₂(Q+1)` for
adversary query budget `Q`. The FS entries describe the FS term, capped below
at zero; the total error is `bindingError + min(1, (Q+1)*2^(-s))` with `s`
from the corresponding IOP column.

| Component | IOP V1 | IOP V2 | IOP V3 | FS V1 | FS V2 | FS V3 |
|---|---:|---:|---:|---:|---:|---:|
| v7 signature | 123 | 191 | 191 | 123−L | 191−L | 191−L |
| v7 hashes | 122 | 125 | 125 | 122−L | 125−L | 125−L |
| v8 signature | 122 | 191 | 191 | 122−L | 191−L | 191−L |
| v8 hashes | 121 | 125 | 125 | 121−L | 125−L | 125−L |

The Ligero development proves:

- Reed–Solomon code distance, affine triple-counting and selected-MCA bounds,
  and JB agreement with checked η³ threshold parameters.
- Response-assisted scalar IOP extraction for Ligero V1, V2, and V3, together
  with response-uniform envelopes and false-statement soundness.
- Merkle prefix binding and typed Fiat–Shamir extraction with total error
  `bindingError + min(1, (Q+1)*epsilon)`.
- Exact IOP and Fiat–Shamir certificates for all v7/v8 signature and hash
  component geometries, across all three Ligero variants.

See [ligero/README.md](ligero/README.md) for the major theorem names, their
formal experiments, and the certified IOP/FS tables. This package also
contains the EC/ECDSA circuit development and existing sumcheck modules.

The [recursive Polygero development](polygero/README.md) proves witness
extraction for the transmitted recursive public-coin verifier, with failure
bound `1 − ∏ᵢ(1 − εᵢ)` from certified local errors. False-statement soundness
is derived from extraction validity and the same failure bound. It reuses
the Ligero code and tableau infrastructure.

From this directory:

```sh
lake build
python3 ligero/examples/Ligero/scripts/audit_envelope_fs.py
```

The package uses Lean 4.31.0 and the compatible Mathlib checkout at
`../../mathlib4`, relative to `formal/`.
