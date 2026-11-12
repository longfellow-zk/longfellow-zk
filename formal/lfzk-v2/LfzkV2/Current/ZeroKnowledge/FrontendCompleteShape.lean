import LfzkV2.Current.ZeroKnowledge.FrontendPads
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteTranscript
import LfzkV2.Current.FrontendTopology

/-! Adapter challenges change coefficients, never the frontend coin or
message shape. These structural equivalences keep one fixed public tape and
one body payload type for every generated circuit. No satisfiability or
privacy property is an input to either transport. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteShape
open SumcheckV2
open scoped Classical
variable {F : Type} [Field F]

def tapeEquiv : {out input : ℕ} → {first second : Layered.Circuit F out input} →
    FrontendTopology.Same first second → CircuitTape first ≃ CircuitTape second
  | _, _, _, _, .input => Equiv.refl _
  | _, _, _, _, .entry (first := first) (second := second) tail =>
      tapeEquiv (first := first) (second := second) tail
  | _, _, _, _, .layer _ tail => Equiv.prodCongr (Equiv.refl _) (tapeEquiv tail)

def payloadEquiv : {out input : ℕ} → {first second : Layered.Circuit F out input} →
    FrontendTopology.Same first second → Layered.Replay.Payload first ≃ Layered.Replay.Payload second
  | _, _, _, _, .input => Equiv.refl _
  | _, _, _, _, .entry (first := first) (second := second) tail =>
      payloadEquiv (first := first) (second := second) tail
  | _, _, _, _, .layer _ tail => Equiv.prodCongr (Equiv.refl _) (payloadEquiv tail)

omit [Field F] in
theorem payloadEquiv_simulate {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : FrontendTopology.Same first second) (tape : CircuitTape first) :
    payloadEquiv same (simulateCircuit first tape) = simulateCircuit second (tapeEquiv same tape) := by
  induction same with
  | input => rfl
  | entry tail ih => exact ih tape
  | layer _ tail ih => exact Prod.ext rfl (ih tape.2)

omit [Field F] in
theorem payloadEquiv_writes {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : FrontendTopology.Same first second) (payload : Layered.Replay.Payload first) :
    FrontendBody.write second (payloadEquiv same payload) = FrontendBody.write first payload := by
  induction same with
  | input => rfl
  | entry tail ih => exact ih payload
  | layer _ tail ih => exact congrArg (List.cons _) (ih payload.2)

def padCount : {out input : ℕ} → {first second : Layered.Circuit F out input} →
    FrontendTopology.Same first second → CellLayout.Pads.count first = CellLayout.Pads.count second
  | _, _, _, _, .input => rfl
  | _, _, _, _, .entry (first := first) (second := second) tail =>
      padCount (first := first) (second := second) tail
  | _, _, _, _, .layer _ tail => congrArg (fun n => _+n) (padCount tail)

theorem tapeEquiv_padValues {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : FrontendTopology.Same first second) (tape : CircuitTape first)
    (i : Fin (CellLayout.Pads.count first)) :
    circuitPadValues second (tapeEquiv same tape) (Fin.cast (padCount same) i) =
      circuitPadValues first tape i := by
  induction same with
  | input => exact Fin.elim0 i
  | entry tail ih => exact ih tape i
  | @layer out mid input assertions firstBody secondBody first second classes tail ih =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        have hc : Fin.cast (padCount (.layer classes tail))
            (Fin.castAdd (CellLayout.Pads.count first) j) =
              Fin.castAdd (CellLayout.Pads.count second) j := by apply Fin.ext; rfl
        simp only [circuitPadValues,tapeEquiv,Equiv.prodCongr_apply,hc,Fin.addCases_left]
        rfl
      · intro j
        have hc : Fin.cast (padCount (.layer classes tail)) (Fin.natAdd (2*mid+4) j) =
            Fin.natAdd (2*mid+4) (Fin.cast (padCount tail) j) := by apply Fin.ext; rfl
        simp only [circuitPadValues,tapeEquiv,Equiv.prodCongr_apply,hc,Fin.addCases_right]
        exact ih tape.2 j

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
