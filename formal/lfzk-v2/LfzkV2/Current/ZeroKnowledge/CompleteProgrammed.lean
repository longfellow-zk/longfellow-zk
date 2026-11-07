import LfzkV2.Current.ZeroKnowledge.CompleteVerifier
import LfzkV2.Current.ZeroKnowledge.OracleProgramming

/-! Acceptance-side transport through the simulator's one opening-answer
replacement. The verifier reads the resulting oracle, including for all
earlier challenges; no cached answers are substituted for those reads. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteProgrammed
open scoped Classical

section Prefix
variable {g : Geometry} {fields : Fields} {Advice Key Block C : Type}
variable (e : OracleProgramming.BodyEncoding (g := g) (fields := fields)
  (Advice := Advice) (Authentication := OpeningBody.Authentication g)
  (Context := Key) (Block := Block) (C := C))
variable (initial : Digest) (body : Body g fields Advice (OpeningBody.Authentication g))
variable (H : Replay.Point g fields Advice (OpeningBody.Authentication g) Key Block → Digest × C)
variable (answer : Digest × C) (i : Fin g.roles.length)

theorem parent_point (before : i.val < g.openingIndex.val) :
    let result := OracleProgramming.programAndFinalize e initial body H g.openingIndex answer
    ((BackendPath.parent e.encoding initial result.1 result.2 i).point :
      Replay.Point g fields Advice (OpeningBody.Authentication g) Key Block) =
      (BackendPath.parent e.encoding initial ⟨body,fun _ => 0⟩ H i).point := by
  simp only [BackendPath.parent_point]
  exact OracleProgramming.programAndFinalize_prefix e initial body H g.openingIndex answer i.val before.le

theorem prior_answers (before : i.val < g.openingIndex.val) :
    let result := OracleProgramming.programAndFinalize e initial body H g.openingIndex answer
    (BackendPath.parent e.encoding initial result.1 result.2 i).point.priorAnswers result.2 =
      (BackendPath.parent e.encoding initial ⟨body,fun _ => 0⟩ H i).point.priorAnswers H := by
  simp only [BackendPath.priorAnswers_replay]
  funext j
  exact congrArg Prod.snd (OracleProgramming.programAndFinalize_answer_before e initial body H
    g.openingIndex answer j.val (j.isLt.trans before))

theorem parent_answer (before : i.val < g.openingIndex.val) :
    let result := OracleProgramming.programAndFinalize e initial body H g.openingIndex answer
    result.2 (BackendPath.parent e.encoding initial result.1 result.2 i).point =
      H (BackendPath.parent e.encoding initial ⟨body,fun _ => 0⟩ H i).point := by
  simp only [BackendPath.parent_point]
  exact OracleProgramming.programAndFinalize_answer_before e initial body H g.openingIndex answer i.val before

end Prefix
end LfzkV2.Current.ZeroKnowledge.CompleteProgrammed
