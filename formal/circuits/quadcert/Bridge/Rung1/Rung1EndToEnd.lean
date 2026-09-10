import quadcert.Core.CommitPacked
import quadcert.Bridge.Rung1.Rung1
import quadcert.Gen.Rung1.Rung1ArtifactCommitment

/-!
# Rung1: committed bytes to handwritten specification

The smallest of the three certificates, and the one to read first.
`Rung1.certified_bytes_accept_iff_spec` says of a single object -- the packed LFC3 payload
`Rung1Artifact.packedInput` -- both of the things a verifier needs:

* those bytes hash to `Rung1Artifact.formalRoot`, the value it pins; and
* whatever circuit they decode to has `Accepts` equivalent to the handwritten elliptic-curve
  specification.

`packedInput` occurs in both conjuncts, so the two halves are visibly about the same bytes.
`Bridge/Sha256/S2EndToEnd.lean` and `Bridge/Ecdsa2/E2EndToEnd.lean` now have the same shape at
their own scale (50 and 13 pages against this one).

## Why the decoded circuit is quantified

`Rung1Artifact.decoded` is defined by a `match` on `decode` with an all-zero fallback, so a
statement mentioning it is silent about whether decoding succeeded -- `decode_ok` rules that out,
but only if the reader goes and looks. Quantifying over `c` with `hdec : decode … = .ok c` in the
statement removes the question: the fallback cannot be the subject of the theorem.

## What is still assumed

Recovering *these* bytes from the root needs SHA-256 collision resistance; the root is a
computational commitment, not an unconditional proof of byte equality. And the production
verifier must pin `formalRoot` against its own binary, which is not a proposition Lean can state.
-/

namespace Rung1

open Quadcert Quadcert.Gen.Rung1

variable {F : Type} [Field F]

/-- The payload's commitment root, phrased over the `PackedBytes` value `Lfc2.decode` consumes
    rather than over a re-spelled leaf list. Definitionally the generated `committed_root`. -/
theorem packedInput_root :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Rung1Artifact.packedInput
      = Quadcert.Gen.Rung1Artifact.formalRoot :=
  Quadcert.Gen.Rung1Artifact.committed_root

/-- `Accepts` for *whatever the committed bytes decode to*, rather than for the generated
    literal. The fallback branch of `Rung1Artifact.decoded` cannot satisfy `hdec`. -/
theorem accepts_decoded_iff_spec [CharP F p256]
    (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.p256 Quadcert.Gen.Rung1Artifact.packedInput = .ok c)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (haCanonical : a = -3) (hbCanonical : b = (bNat : F))
    (inputs : Nat → F) (hone : inputs Layout.one = 1)
    (params : CurveParameters F) (hpa : params.a = a) (hpb : params.b = b) :
    Accepts ((c.toRaw advice).toQuad (artifactConsts F)) inputs
      ↔ (inputs Layout.qz * inputs Layout.zinv = 1
          ∧ ProjectiveEquiv
              ⟨inputs Layout.qx, inputs Layout.qy, inputs Layout.qz⟩
              (AffinePoint.mk (inputs Layout.px) (inputs Layout.py)).toProjective
          ∧ AffinePoint.IsOnCurve ⟨inputs Layout.px, inputs Layout.py⟩ params) := by
  have hc : c = Quadcert.Gen.Rung1Artifact.decoded := by
    have h := hdec.symm.trans Quadcert.Gen.Rung1Artifact.decode_ok
    simpa using h
  subst hc
  exact accepts_artifact_iff_spec a b ha hb haCanonical hbCanonical inputs hone params hpa hpb

/-- **The Rung1 certificate.** The committed payload hashes to the pinned root, and any
    accepting witness for the circuit it decodes to satisfies the specification. -/
theorem certified_bytes_accept_iff_spec [CharP F p256]
    (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.p256 Quadcert.Gen.Rung1Artifact.packedInput = .ok c)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (haCanonical : a = -3) (hbCanonical : b = (bNat : F))
    (inputs : Nat → F) (hone : inputs Layout.one = 1)
    (params : CurveParameters F) (hpa : params.a = a) (hpb : params.b = b) :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Rung1Artifact.packedInput
        = Quadcert.Gen.Rung1Artifact.formalRoot
      ∧ (Accepts ((c.toRaw advice).toQuad (artifactConsts F)) inputs
          ↔ (inputs Layout.qz * inputs Layout.zinv = 1
              ∧ ProjectiveEquiv
                  ⟨inputs Layout.qx, inputs Layout.qy, inputs Layout.qz⟩
                  (AffinePoint.mk (inputs Layout.px) (inputs Layout.py)).toProjective
              ∧ AffinePoint.IsOnCurve ⟨inputs Layout.px, inputs Layout.py⟩ params)) :=
  ⟨packedInput_root,
   accepts_decoded_iff_spec c hdec a b ha hb haCanonical hbCanonical inputs hone params hpa hpb⟩

/-- Retained under its original name. -/
theorem artifact_bytes_commit_to_formalRoot :
    QuadCert.CircuitCommitment.rootFromLeaves 297
      [QuadCert.CircuitCommitment.packedLeafHash 297 0 297
        Quadcert.Gen.Rung1Artifact.packedPage_0]
      = Quadcert.Gen.Rung1Artifact.formalRoot :=
  Quadcert.Gen.Rung1Artifact.committed_root

end Rung1
