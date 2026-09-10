import quadcert.Core.CommitPacked
import quadcert.Gen.MdocSig.MdocSigDecode
import quadcert.Gen.MdocSig.MdocSigCommitment

/-!
# The mdoc signature circuit's artifact

**Step 1 for a deployed mdoc circuit.** Everything proved about mdoc so far has been step 4 —
`circuits/mdoc/` states what the two circuits are supposed to establish and proves that their
assertion sets imply it. Nothing until now connected either statement to the bytes a verifier
actually loads. This does, for the signature half.

## Where the bytes come from

The shipped artifact bundles both circuits in one zstd'd LFA2 archive, so neither can be read on
its own and `lfc3_to_lean` — which takes a bare LFC2 blob — had nothing to eat. `mdoc_lfc2`
splits them:

```bash
cargo run --release -p mdoc-zk-runtime --bin mdoc_lfc2 -- OUT_DIR [CIRCUIT_HASH]
cargo run --release -p core-proto --example lfc3_to_lean -- \
    p256 OUT_DIR/mdoc_sig.lfc2 ../formal/circuits/quadcert MdocSig
```

Both halves are **segmented before writing**, because `segment_circuit` renumbers every
`k_index`; the artifact and anything built beside it have to come from the same circuit.

## The numbers

21 layers, 481,833 terms, 1,634 constants, `ninput = 3739`, 478,823 committed bytes in 117 pages. For
comparison the largest artifact previously ingested is `Sha256Blk` at 203,104 bytes in 50 pages,
and `Sha256Gf2` at 28,327 in 7. The mdoc *hash* circuit is 16× larger again — see
`MHashArtifact.lean` when it lands.

## Naming

`MSig`, not `MdocSig`. Regeneration deletes the `<Name>*` glob before writing, and a handwritten
module that answers to it gets destroyed — which is how `quadcert/Sha256.lean` was lost once, and
why the other handwritten bridges are `S2*`, `E2*` and `Gf2*`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace MdocSig

open Quadcert Quadcert.Gen.MdocSig

/-- The 117 packed pages hash to the pinned root, phrased over the payload `Lfc2.decode`
    consumes. Same shape as `Sha256Gf2.packedInput_root` and `Sha256Blk.packedInput_root`. -/
theorem packedInput_root :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.MdocSig.packedInput
      = Quadcert.Gen.MdocSig.formalRoot :=
  Quadcert.Gen.MdocSig.committed_root

/-- **The committed bytes decode.** Quantified over the result rather than naming the generated
    literal, so the statement is about the bytes. -/
theorem certified_bytes_decode (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.p256 packedInput deltaTrees = .ok c) :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.MdocSig.packedInput
        = Quadcert.Gen.MdocSig.formalRoot
      ∧ c = Quadcert.Gen.MdocSig.decoded :=
  ⟨packedInput_root, by
    have h := hdec.symm.trans Quadcert.Gen.MdocSig.decode_ok
    simpa using h⟩

end MdocSig
