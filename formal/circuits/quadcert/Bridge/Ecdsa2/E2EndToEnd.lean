import quadcert.Core.CommitPacked
import quadcert.Gen.E2.E2Ecdsa
import quadcert.Gen.Ecdsa2.Ecdsa2Commitment

/-!
# ECDSA2: committed bytes to the ECDSA specification

`ecdsa2_sound_of_bytes` quantifies over the decode -- its hypothesis is
`Lfc2.decode p256 packedInput deltaTrees = .ok c` -- but says nothing about the commitment, so
on its own it does not tell a reviewer that `packedInput` is the deployed artifact rather than
some list of numbers a generator wrote down.  `Ecdsa2Commitment.committed_root` supplies the
missing half, and this file joins them.

`ecdsa2_certified_bytes` states both about one term.  `packedInput` occurs in the root
conjunct and in `hdec`, so the bytes that hash to `formalRoot` are syntactically the bytes that
decode to the circuit `hacc` is about.

Recovering *these* bytes from the root needs SHA-256 collision resistance; the root is a
computational commitment, not an unconditional proof of byte equality.  And the production
verifier must pin `formalRoot` against its own binary, which is not a proposition Lean can
state.  See `Bridge/Rung1/Rung1EndToEnd.lean` for the same composition at Rung1's scale.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Ecdsa2.Assembly

open Quadcert Quadcert.Gen.Ecdsa2 Ecdsa2.Meaning ECDSA2

variable {F : Type} [Field F] [CharP F p256]

/-- The artifact's 13 packed LFC3 pages hash to the pinned root, phrased over the payload
    `Lfc2.decode` consumes rather than over a re-spelled leaf list.  Definitionally the
    generated `committed_root`; the page indices and the 820-byte final page come from
    `packedInput` itself. -/
theorem packedInput_root :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Ecdsa2.packedInput
      = Quadcert.Gen.Ecdsa2.formalRoot :=
  Quadcert.Gen.Ecdsa2.committed_root

/-- **The ECDSA2 certificate.** The committed payload hashes to the pinned root, and any
    accepting witness for the circuit those same bytes decode to yields a standard ECDSA
    verification for the public key, message hash and signature read off the input layout. -/
theorem ecdsa2_certified_bytes
    (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.p256 Quadcert.Gen.Ecdsa2.packedInput
      Quadcert.Gen.Ecdsa2.deltaTrees = .ok c)
    (inputs : Nat → F) (hone : inputs 0 = 1)
    (params : CurveParameters F) [(params.toMathlib).IsElliptic]
    [CurveHasNoPointsOfOrder2 params] (order : Nat) [Fact (Nat.Prime order)]
    (ha : params.a = -3)
    (hb : params.b = (41058363725152142129326129780047268409114441015993725554835256314039467401291 : F))
    (hgx : params.gx = (48439561293906451759052585252797914202762949526041747995844080717082404635286 : F))
    (hgy : params.gy = (36134250956749795798585127919587881956611106672985015071877198253568414405109 : F))
    (hk : params.kBits = 256)
    (horder : order = 115792089210356248762697446949407573529996955224135760342422259061068512044369)
    (hacc : Accepts ((c.toRaw advice).toQuad (Ecdsa2.consts F)) inputs)
    (h_G_on : ProjectivePoint.IsOnCurve
      ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params)
    (h_pk_order : bsmul (padBits (natToBits order) params.kBits)
      ({ X := inputs 1, Y := inputs 2 : AffinePoint F }).toProjective params = infinityPoint)
    (h_G_order : ProjectiveEquiv (bsmul (padBits (natToBits order) params.kBits)
      ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) infinityPoint)
    (h_R_order : ProjectiveEquiv (bsmul (padBits (natToBits order) params.kBits)
      ({ X := inputs 4, Y := inputs 5 : AffinePoint F }).toProjective params) infinityPoint) :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Ecdsa2.packedInput
        = Quadcert.Gen.Ecdsa2.formalRoot
      ∧ ∃ (r s e_nat : Nat),
          r = natR (((usList inputs).map ECDSA2.bitrev3).map val3) ∧
          s = order - natS (((usList inputs).map ECDSA2.bitrev3).map val3) ∧
          e_nat = natE (((usList inputs).map ECDSA2.bitrev3).map val3) ∧
          StandardEcdsaVerify ({ X := inputs 1, Y := inputs 2 : AffinePoint F })
            e_nat r s order params :=
  ⟨packedInput_root,
   ecdsa2_sound_of_bytes c hdec inputs hone params order ha hb hgx hgy hk horder hacc
     h_G_on h_pk_order h_G_order h_R_order⟩

end Ecdsa2.Assembly
