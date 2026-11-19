import LfzkV2.Current.ZeroKnowledge.FrontendReplay
import LfzkV2.Current.ZeroKnowledge.FrontendLayerAnswerTape

/-! The stateful frontend compiler consumes exactly the answer coordinates
that the verifier later replays. This includes shared entry/assertion
coefficients, and later weights and input assertions extending the
preceding combine answer. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape

open SumcheckV2
open scoped Classical
set_option maxHeartbeats 1000000
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C F Pad : Type} [Field F]
variable (side : Side) (field : fields side ≃ F)
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
variable (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (fallback : C)

/-- A layer's weights: the opening answer's coordinates, or the preceding
combine answer's coordinates after alpha. -/
theorem open_facts (count : ℕ) (state future : CompleteTranscript.State g fields Advice Key Base C)
    (continuing : Bool) (last : continuing = true → Last fallback state)
    (positive : continuing = true → 0 < state.rank.val)
    (inside : continuing = false → state.rank.val < g.roles.length)
    (extended : Extends fallback
      (inputCoefficients (CompleteTranscript.reader side field decode nonzero base H) continuing state count).2
        future) :
    let opened := inputCoefficients (CompleteTranscript.reader side field decode nonzero base H) continuing state count
    let start := if continuing then state.rank.val-1 else state.rank.val
    opened.2.rank.val = start+1 ∧ Last fallback opened.2 ∧
      opened.1 = (fun i => decode (lookup fallback future start) ((if continuing then 1 else 0)+i.val)) ∧
      Extends fallback state opened.2 := by
  cases continuing with
  | false =>
      have hin := inside rfl
      refine ⟨?_,?_,?_,?_⟩
      · change (CompleteTranscript.step base H state).2.rank.val = state.rank.val+1
        rw [SimulationWrites.step_rank]
        exact Nat.min_eq_right (by omega)
      · exact step_last_inside base H fallback state hin
      · change (fun i : Fin count => decode (CompleteTranscript.step base H state).1 i.val) = _
        rw [step_answer_into base H fallback state future hin extended]
        funext i
        simp
      · exact step_extends base H fallback state
  | true =>
      have hpos := positive rfl
      refine ⟨by change state.rank.val = state.rank.val-1+1; omega,last rfl,?_,Extends.refl fallback state⟩
      change (fun i : Fin count => decode state.lastAnswer (1+i.val)) = _
      have hvalue : state.lastAnswer = lookup fallback future (state.rank.val-1) :=
        (last rfl).trans (extended.2 _ (by change state.rank.val-1 < state.rank.val; omega)).symm
      rw [hvalue]
      rfl

theorem readSetup_into {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit)
    (state future : CompleteTranscript.State g fields Advice Key Base C) (continuing : Bool)
    (last : continuing = true → Last fallback state)
    (positive : continuing = true → 0 < state.rank.val)
    (fits : state.rank.val+Frontend.ScheduleLength.circuitFuel plan continuing ≤ g.roles.length)
    (extended : Extends fallback
      (readSetup (CompleteTranscript.reader side field decode nonzero base H)
        plan ids payload state continuing).2 future) :
    messagesFromSetup circuit
      (readSetup (CompleteTranscript.reader side field decode nonzero base H)
        plan ids payload state continuing).1 payload =
      FrontendReplay.readFrom decode nonzero circuit ids payload (lookup fallback future)
        (replayStart circuit state.rank.val continuing) (replayOffset circuit continuing) := by
  induction plan generalizing state future continuing with
  | input => rfl
  | inputEntry =>
      cases continuing with
      | false =>
          have inside : state.rank.val < g.roles.length := by
            simp only [Frontend.ScheduleLength.circuitFuel,Bool.false_eq_true,↓reduceIte] at fits
            omega
          have answer := step_answer_into base H fallback state future inside extended
          simp only [readSetup,inputCoefficients,Bool.false_eq_true,↓reduceIte,
            CompleteTranscript.reader,messagesFromSetup,replayStart,replayOffset,
            FrontendReplay.readFrom,Nat.zero_add]
          rw [answer]
      | true =>
          change Extends fallback state future at extended
          have value : state.lastAnswer = lookup fallback future (state.rank.val-1) :=
            (last rfl).trans (extended.2 _ (by have := positive rfl; omega)).symm
          simp only [readSetup,inputCoefficients,↓reduceIte,CompleteTranscript.reader,messagesFromSetup,
            replayStart,replayOffset,FrontendReplay.readFrom]
          rw [value]
  | @layer out mid input assertions body rest metadata tail ih =>
      let opened := inputCoefficients (CompleteTranscript.reader side field decode nonzero base H)
        continuing state assertions
      let replay := readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader opened.2 payload.1
      have fuel : Frontend.ScheduleLength.circuitFuel (.layer metadata tail) continuing =
          Frontend.ScheduleLength.circuitFuel tail true+(2+mid)+(if continuing then 0 else 1) := rfl
      have through := (readSetup_extends base H side field decode nonzero fallback
        tail ids.2 payload.2 replay.state true).trans extended
      have layerThrough := (layer_extends side field base H decode nonzero fallback opened.2 payload.1).trans through
      have facts := open_facts side field base H decode nonzero fallback assertions state future continuing last
        positive (fun h => by rw [fuel, h] at fits; simp at fits; omega) layerThrough
      obtain ⟨openRank,openLast,openCoefficients,_⟩ := facts
      have hs : (if continuing then state.rank.val-1 else state.rank.val)+1 =
          state.rank.val+(if continuing then 0 else 1) := by
        cases continuing
        · rfl
        · have := positive rfl
          simp only [↓reduceIte]
          omega
      have layerFits : opened.2.rank.val+mid+2 ≤ g.roles.length := by
        rw [openRank]
        rw [fuel] at fits
        omega
      have layer := layer_properties_into side field base H decode nonzero fallback opened.2 future payload.1
        layerFits through
      have tailFits : replay.state.rank.val+Frontend.ScheduleLength.circuitFuel tail true ≤ g.roles.length := by
        rw [layer.1,openRank]
        rw [fuel] at fits
        omega
      have tailEq := ih ids.2 payload.2 replay.state future true
        (fun _ => layer_last side field base H decode nonzero fallback opened.2 payload.1 openLast)
        (fun _ => by rw [layer.1]; omega) tailFits extended
      have replayRank : replay.state.rank.val = (if continuing then state.rank.val-1 else state.rank.val)+mid+3 := by
        rw [layer.1,openRank]; omega
      simp only [replayStart,replayOffset,↓reduceIte,replayRank] at tailEq
      rw [show (if continuing then state.rank.val-1 else state.rank.val)+mid+3-1 =
        (if continuing then state.rank.val-1 else state.rank.val)+mid+2 by omega] at tailEq
      dsimp only [readSetup,messagesFromSetup,setupLayer]
      apply Prod.ext
      · have hp := layer.2.1
        have hsc := layer.2.2.1
        have ha := layer.2.2.2
        simp only [opened] at hp hsc ha openRank openCoefficients
        rw [openRank] at hp hsc ha
        rw [show (if continuing then state.rank.val-1 else state.rank.val)+1+mid+1 =
          (if continuing then state.rank.val-1 else state.rank.val)+mid+2 by omega] at ha
        simp only [openCoefficients,replayStart,replayOffset,FrontendReplay.readFrom,linearPlan,hp,hsc,ha]
      · exact tailEq
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      let opened := inputCoefficients (CompleteTranscript.reader side field decode nonzero base H)
        continuing state (checks+assertions)
      let replay := readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader opened.2 payload.1
      have fuel : Frontend.ScheduleLength.circuitFuel (.entryLayer entries entry metadata tail) continuing =
          Frontend.ScheduleLength.circuitFuel tail true+(2+mid)+(if continuing then 0 else 1) := rfl
      have through := (readSetup_extends base H side field decode nonzero fallback
        tail ids.2 payload.2 replay.state true).trans extended
      have layerThrough := (layer_extends side field base H decode nonzero fallback opened.2 payload.1).trans through
      have facts := open_facts side field base H decode nonzero fallback (checks+assertions) state future continuing
        last positive (fun h => by rw [fuel, h] at fits; simp at fits; omega) layerThrough
      obtain ⟨openRank,openLast,openCoefficients,_⟩ := facts
      have hs : (if continuing then state.rank.val-1 else state.rank.val)+1 =
          state.rank.val+(if continuing then 0 else 1) := by
        cases continuing
        · rfl
        · have := positive rfl
          simp only [↓reduceIte]
          omega
      have layerFits : opened.2.rank.val+mid+2 ≤ g.roles.length := by
        rw [openRank]
        rw [fuel] at fits
        omega
      have layer := layer_properties_into side field base H decode nonzero fallback opened.2 future payload.1
        layerFits through
      have tailFits : replay.state.rank.val+Frontend.ScheduleLength.circuitFuel tail true ≤ g.roles.length := by
        rw [layer.1,openRank]
        rw [fuel] at fits
        omega
      have tailEq := ih ids.2 payload.2 replay.state future true
        (fun _ => layer_last side field base H decode nonzero fallback opened.2 payload.1 openLast)
        (fun _ => by rw [layer.1]; omega) tailFits extended
      have replayRank : replay.state.rank.val = (if continuing then state.rank.val-1 else state.rank.val)+mid+3 := by
        rw [layer.1,openRank]; omega
      simp only [replayStart,replayOffset,↓reduceIte,replayRank] at tailEq
      rw [show (if continuing then state.rank.val-1 else state.rank.val)+mid+3-1 =
        (if continuing then state.rank.val-1 else state.rank.val)+mid+2 by omega] at tailEq
      dsimp only [readSetup,messagesFromSetup,setupLayer]
      apply Prod.ext
      · rw [openCoefficients]
        simp only [replayStart,replayOffset,FrontendReplay.readFrom]
      · apply Prod.ext
        · have hp := layer.2.1
          have hsc := layer.2.2.1
          have ha := layer.2.2.2
          simp only [opened] at hp hsc ha openRank openCoefficients
          rw [openRank] at hp hsc ha
          rw [show (if continuing then state.rank.val-1 else state.rank.val)+1+mid+1 =
            (if continuing then state.rank.val-1 else state.rank.val)+mid+2 by omega] at ha
          simp only [openCoefficients,replayStart,replayOffset,FrontendReplay.readFrom,linearPlan,hp,hsc,ha,
            Nat.add_assoc]
        · exact tailEq

theorem readSetup_initial_into {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit)
    (state future : CompleteTranscript.State g fields Advice Key Base C)
    (fits : state.rank.val+Frontend.ScheduleLength.circuitFuel plan false ≤ g.roles.length)
    (extended : Extends fallback
      (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state false).2 future) :
    messagesFromSetup circuit
      (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state false).1 payload =
      FrontendReplay.readFrom decode nonzero circuit ids payload (lookup fallback future) state.rank.val 0 := by
  simpa only [replayStart,replayOffset,Bool.false_eq_true,↓reduceIte] using
    readSetup_into side field base H decode nonzero fallback plan ids payload state future false
      (by simp) (by simp) fits extended

theorem replay_shift {out input : ℕ} (circuit : Layered.Circuit F out input)
    (ids : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (origin start offset : ℕ) :
    FrontendReplay.readFrom decode nonzero circuit ids payload answers (origin+start) offset =
      FrontendReplay.readFrom decode nonzero circuit ids payload (fun q => answers (origin+q)) start offset := by
  induction circuit generalizing start offset with
  | input => rfl
  | entry checks _ _ ih =>
      exact congrArg (fun tail => ((fun i : Fin checks => decode (answers (origin+start)) (offset+i.val)),tail))
        (ih ids payload start (offset+checks))
  | @layer out mid input assertions body rest ih =>
      simp only [FrontendReplay.readFrom]
      apply Prod.ext
      · simp only [Nat.add_assoc]
      · simpa only [Nat.add_assoc] using ih ids.2 payload.2 (start+mid+2) 1

end LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape
