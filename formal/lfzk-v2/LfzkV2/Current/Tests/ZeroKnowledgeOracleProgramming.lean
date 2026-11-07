import LfzkV2.Current.ZeroKnowledge.OracleOpening
import Lean.Util.CollectAxioms

/-! These endpoints distinguish the one complete programmed answer from a
challenge-only patch and keep finalization tied to the actual proof body. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleProgramming
open ZeroKnowledge.OracleProgramming
open scoped Classical

section Replay
variable {P Link C Out : Type} {R : ℕ}
variable (chain : TranscriptV2.Chain P Link C Out R) (output : Out)
variable (H : P → Link × C) (cut : Fin R) (link : Link) (challenge : C)

example :
    (program chain output H cut (link,challenge)
      (chain.point output (program chain output H cut (link,challenge)) cut.val)).1 = link ∧
    (program chain output H cut (link,challenge)
      (chain.point output (program chain output H cut (link,challenge)) cut.val)).2 = challenge := by
  rw [answer_at]
  exact ⟨rfl,rfl⟩

example (index : ℕ) (earlier : index < cut.val) :
    program chain output H cut (link,challenge)
        (chain.point output (program chain output H cut (link,challenge)) index) =
      H (chain.point output H index) :=
  answer_before chain output H cut (link,challenge) index earlier
end Replay

section Body
variable {g : Geometry} {fields : Fields} {Advice Auth Key Block C : Type}
variable (encoder : BodyEncoding (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Auth) (Context := Key) (Block := Block) (C := C))
variable (body : Body g fields Advice Auth) (initial : Digest)
variable (H : Replay.Point g fields Advice Auth Key Block → Digest × C)
variable (cut : Fin g.roles.length) (answer : Digest × C)

example :
    let result := programAndFinalize encoder initial body H cut answer
    result.1.body.authentication = body.authentication ∧
      result.2 ((encoder.encoding.chain initial).point result.1 result.2 cut.val) = answer ∧
      (result.2 ((encoder.encoding.chain initial).finalSealPoint result.1 result.2)).1 =
        result.1.finalSeal := by
  exact ⟨rfl,programAndFinalize_answer encoder initial body H cut answer,
    programAndFinalize_seal encoder initial body H cut answer⟩
end Body

#print axioms answer_at
#print axioms programAndFinalize_answer
#print axioms programAndFinalize_seal
#print axioms ZeroKnowledge.OracleOpening.point_off

end LfzkV2.Current.Tests.ZeroKnowledgeOracleProgramming
