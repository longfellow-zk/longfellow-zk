import quadcert.Core.CommitPacked
import quadcert.Gen.MdocHash.MdocHashPacked
import quadcert.Gen.MdocHash.MdocHashCommitment

/-!
# The mdoc hash circuit's artifact

The other half of `MSigArtifact.lean`, and the one the size warnings were about. This is the
circuit `circuits/mdoc/` spends all its effort on: SHA-256 over the COSE `Signature1` buffer, the
CBOR window checks, the three GF(2¹²⁸) MACs.

## The numbers, measured rather than assumed

Artifact `8d0792117152…` — v7, **one** disclosed attribute:

| | layers | terms | LFC3 bytes | pages | Lean modules |
|---|---:|---:|---:|---:|---:|
| this circuit | 17 | 7,757,579 | 968,323 | 237 | 8,497 |
| `Gen/Sha256Blk`, the largest before it | 6 | 98,993 | 203,104 | 50 | 1,109 |

`5aebdaaa…` is the four-attribute variant at 9,063,890 terms / 287 pages; those are the figures in
`LFC3_PROTOCOL.md`. The signature circuit is identical across every variant.

## Why this is tractable at all

Two things, both measured by `mdoc_layer_probe`:

* **It compresses.** `sym/trm` is 0.01–0.2 on almost every layer. One-block SHA-256's LFC3 does
  not compress at all, which made its parse modules ~10× denser than ECDSA2's at comparable size —
  and *that*, not size, is what made them unbuildable. The failure mode does not transfer.
* **The lookup was the cost, and it is already fixed.** Expanding this circuit with `Array`'s
  `deltas[i]?` list walk is 42.2 CPU-hours; with `Core/Lfc3.lean`'s `PTree` it is 2.2 CPU-minutes.
  `CompressedLayer.deltaAt_eq` is what makes the tree admissible — it is untrusted advice, tied
  back to the decoded list by `checkSize` and `toList`. The tree's docstring names these layers as
  the case it was written for.

The remaining bulk is the 7,584 expansion chunks, which are wide but shallow: **3 s each** once
their layer's parse chain is built, so about six hours serial and trivially parallel.

## What is here, and what is not

`packedInput_root` — the 237 pages hash to the pinned root — is proved. `certified_bytes_decode`
is **not**, and the reason is disk rather than mathematics.

An expansion module's `.olean` is 3.53 MB (measured on `MdocHashExpansion1_0`, 22 KB of source —
the elaborated form is ~155× the text). Times 7,584 that is **26.8 GB**, and regenerating at
8192-term chunks brings it to ~955 modules and **~18 GB**, which is the floor: at that chunk size
the per-module overhead is already amortised. There was 12 GB free.

So the expansion modules are *not checked in*. Regenerating them is three minutes:

```bash
cargo run --release -p mdoc-zk-runtime --bin mdoc_lfc2 -- OUT_DIR \
  8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121
cargo run --release -p core-proto --example lfc3_to_lean -- \
  gf2_128 OUT_DIR/mdoc_hash.lfc2 ../formal/circuits/quadcert MdocHash 8192
```

and then `tools/leanseq quadcert 20 '^Gen\.MdocHash'`. Restoring the `certified_bytes_decode`
below is re-adding the `MdocHashDecode` import and the theorem; it is written out in
`MSigArtifact.lean`, which does have its expansion chain, against the same generated names.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace MdocHash

open Quadcert Quadcert.Gen.MdocHash

/-- The 237 packed pages hash to the pinned root, phrased over the payload `Lfc3.decode`
    consumes. -/
theorem packedInput_root :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.MdocHash.packedInput
      = Quadcert.Gen.MdocHash.formalRoot :=
  Quadcert.Gen.MdocHash.committed_root

end MdocHash
