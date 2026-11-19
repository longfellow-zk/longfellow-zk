import LfzkV2.Current.ZeroKnowledge.FrontendPads
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteTranscript

/-! The body payload of a planned circuit, in the frontend message layout of
its public schedule. The binary circuit is fixed, so no transport between
circuit instances is needed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteShape
open SumcheckV2
open scoped Classical
variable {F : Type} [Field F]

def layerBodyEquiv (n : ℕ) : Layered.Replay.LayerPayload F n ≃ Current.LayerPayload F n where
  toFun payload := ⟨fun i => ((payload.rounds i).c0,(payload.rounds i).c1),
    payload.cross,(payload.claimA,payload.claimB)⟩
  invFun := FrontendBody.layer id
  left_inv payload := by
    cases payload with
    | mk rounds cross a b =>
        congr 1
  right_inv payload := by cases payload; rfl

def consEquiv (head : Stage) (tail : Frontend) :
    (Current.LayerPayload F head.rounds × Current.FrontendPayload F tail) ≃
      Current.FrontendPayload F ⟨head :: tail.stages,tail.inputEntries⟩ where
  toFun payload := Fin.cases payload.1 payload.2
  invFun payload := (payload 0,fun i => payload i.succ)
  left_inv _ := rfl
  right_inv payload := by
    funext i
    cases i using Fin.cases <;> rfl

def bodyEquiv : {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    (plan : FrontendSchedule.Plan F circuit) →
      Layered.Replay.Payload circuit ≃ Current.FrontendPayload F plan.frontend
  | _, _, _, .input =>
      ⟨fun _ i => Fin.elim0 i,fun _ => (),fun _ => rfl,fun _ => funext fun i => Fin.elim0 i⟩
  | _, _, _, .inputEntry _ _ =>
      ⟨fun _ i => Fin.elim0 i,fun _ => (),fun _ => rfl,fun _ => funext fun i => Fin.elim0 i⟩
  | _, _, _, .layer (mid := mid) metadata tail =>
      (Equiv.prodCongr (layerBodyEquiv mid) (bodyEquiv tail)).trans
        (consEquiv ⟨[],metadata.fragments,mid⟩ tail.frontend)
  | _, _, _, .entryLayer (mid := mid) entries _ metadata tail =>
      (Equiv.prodCongr (layerBodyEquiv mid) (bodyEquiv tail)).trans
        (consEquiv ⟨entries.entries,metadata.fragments,mid⟩ tail.frontend)

omit [Field F] in
theorem stages_bodyEquiv {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (payload : Layered.Replay.Payload circuit) :
    FrontendBody.stages plan.frontend (bodyEquiv plan payload) = FrontendBody.write circuit payload := by
  induction plan with
  | input => rfl
  | inputEntry => rfl
  | layer _ _ ih =>
      simp only [FrontendBody.stages,FrontendSchedule.Plan.frontend,List.length_cons,
        List.finRange_succ,List.map_cons,List.map_map,List.get_cons_zero,
        bodyEquiv,consEquiv,FrontendBody.write]
      exact congrArg (List.cons _) (ih payload.2)
  | entryLayer _ _ _ _ ih =>
      simp only [FrontendBody.stages,FrontendSchedule.Plan.frontend,List.length_cons,
        List.finRange_succ,List.map_cons,List.map_map,List.get_cons_zero,
        bodyEquiv,consEquiv,FrontendBody.write]
      exact congrArg (List.cons _) (ih payload.2)

omit [Field F] in
theorem decode_bodyEquiv {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (payload : Layered.Replay.Payload circuit) :
    FrontendBody.decode id circuit plan.frontend (bodyEquiv plan payload) = some payload := by
  rw [FrontendBody.decode,stages_bodyEquiv]
  exact FrontendBody.read_write circuit payload

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteShape
