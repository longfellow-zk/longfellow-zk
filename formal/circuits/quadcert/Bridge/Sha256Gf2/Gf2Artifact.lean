import quadcert.Core.CommitPacked
import quadcert.Gen.Sha256Gf2.Sha256Gf2Decode
import quadcert.Gen.Sha256Gf2.Sha256Gf2Commitment

/-!
# The GF(2^128) SHA-256 artifact

The same one-block SHA-256 circuit as `Gen/Sha256Blk`, compiled over the field the deployed mdoc
*hash* circuit actually uses. Both come from `sha256_artifacts`, which now takes
`--field=p256|gf2_128`; the p256 run still reproduces `9f3fab77…` byte for byte.

Two things this establishes that nothing previously did.

**`Lfc2.decode` works at `gf2_128` on a real artifact.** Until now the binary-field encoding had
only three unit tests in `Core/Lfc2Test.lean`. `Sha256Gf2Decode.decode_ok` runs the whole staged
parse — 12 layers, 233 modules — and lands on the generated `decoded` literal.

**The binary-field artifact is much cheaper.** 28,327 bytes in 7 pages against the p256
artifact's 203,104 in 50, and the worst layer holds 1,048 distinct deltas against 11,952 — the
layer that forced `Lfc2Chunk` on the p256 side. The multiplicative injection is a product tree of
degree-2 nodes, which segments; the positional one is a 32-term sum with 32 distinct
coefficients, which does not.
-/

set_option maxRecDepth 1000000

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

/-- The seven packed pages hash to the pinned root, phrased over the payload `Lfc2.decode`
    consumes. Same shape as `Rung1.packedInput_root` and `Sha256Blk.packedInput_root`. -/
theorem packedInput_root :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Sha256Gf2.packedInput
      = Quadcert.Gen.Sha256Gf2.formalRoot :=
  Quadcert.Gen.Sha256Gf2.committed_root

/-- **The committed bytes decode.** Quantified over the result rather than naming the generated
    literal, so the statement is about the bytes. -/
theorem certified_bytes_decode (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.gf2_128 packedInput deltaTrees = .ok c) :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Sha256Gf2.packedInput
        = Quadcert.Gen.Sha256Gf2.formalRoot
      ∧ c = Quadcert.Gen.Sha256Gf2.decoded :=
  ⟨packedInput_root, by
    have h := hdec.symm.trans Quadcert.Gen.Sha256Gf2.decode_ok
    simpa using h⟩

end Sha256Gf2
