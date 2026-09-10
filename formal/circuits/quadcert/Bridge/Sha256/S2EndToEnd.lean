import quadcert.Core.CommitPacked
import quadcert.Bridge.Sha256.S2Bytes
import quadcert.Gen.Sha256Blk.Sha256BlkCommitment

/-!
# SHA-256: committed bytes to `SHA/Spec.lean`

`sha256_block_of_bytes` quantifies over the decode -- its hypothesis is
`Lfc2.decode p256 packedInput deltaTrees = .ok c` -- but says nothing about the commitment, so
on its own it does not tell a reviewer that `packedInput` is the deployed artifact rather than
some list of numbers a generator wrote down.  `Sha256BlkCommitment.committed_root` supplies the
missing half, and this file joins them.

`sha256_certified_bytes` states both about one term.  `packedInput` occurs in the root conjunct
and in `hdec`, so the 203,104 bytes that hash to `formalRoot` are syntactically the bytes that
decode to the circuit `hacc` is about.

Recovering *these* bytes from the root needs SHA-256 collision resistance; the root is a
computational commitment, not an unconditional proof of byte equality.  And the production
verifier must pin `formalRoot` against its own binary, which is not a proposition Lean can
state.  See `Bridge/Rung1/Rung1EndToEnd.lean` for the same composition at Rung1's scale.
-/

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

/-- The artifact's 50 packed LFC3 pages hash to the pinned root, phrased over the payload
    `Lfc2.decode` consumes rather than over a re-spelled leaf list.  Definitionally the
    generated `committed_root`; the page indices and the 2,400-byte final page come from
    `packedInput` itself. -/
theorem packedInput_root :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Sha256Blk.packedInput
      = Quadcert.Gen.Sha256Blk.formalRoot :=
  Quadcert.Gen.Sha256Blk.committed_root

variable {F : Type} [Field F]

/-- **The SHA-256 certificate.** The committed payload hashes to the pinned root, and any
    accepting witness for the circuit those same bytes decode to has its eight outgoing
    chaining words equal to `SHA256.blockFrom` of the incoming ones and the message block. -/
theorem sha256_certified_bytes (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.p256 packedInput deltaTrees = .ok c)
    [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hacc : Accepts ((c.toRaw advice).toQuad (consts F)) inputs) :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Sha256Blk.packedInput
        = Quadcert.Gen.Sha256Blk.formalRoot
      ∧ (List.range 8).map (outWord inputs)
          = SHA256.blockFrom ((List.range 8).map (hWord inputs)) (msgBlock inputs) :=
  ⟨packedInput_root, sha256_block_of_bytes c hdec inputs hin0 hacc⟩

end Sha256Blk
