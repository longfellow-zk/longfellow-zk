import LfzkV2.Current.ZeroKnowledge.FrontendLayerAnswerTape
import LfzkV2.Current.ZeroKnowledge.FrontendReplay

/-! The stateful frontend compiler consumes exactly the answer coordinates
that the verifier later replays. This includes shared entry/assertion
coefficients and input assertions extending the final combine answer. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape

open SumcheckV2
open scoped Classical
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C F Pad : Type} [Field F]
variable (side : Side) (field : fields side ≃ F)
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
variable (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (fallback : C)

theorem head_rank {n : ℕ} (state : CompleteTranscript.State g fields Advice Key Base C)
    (payload : LayerPayload F n) (fits : state.rank.val+n+3 ≤ g.roles.length) :
    (readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader
      (CompleteTranscript.step base H state).2 payload).state.rank.val = state.rank.val+n+3 := by
  have first : (CompleteTranscript.step base H state).2.rank.val = state.rank.val+1 := by
    rw [SimulationWrites.step_rank]
    exact Nat.min_eq_right (by omega)
  have next := layer_properties side field base H decode nonzero state.lastAnswer
    (CompleteTranscript.step base H state).2 payload (by rw [first]; omega)
  rw [next.1,first]
  omega

theorem head_last {n : ℕ} (state : CompleteTranscript.State g fields Advice Key Base C)
    (payload : LayerPayload F n) (fits : state.rank.val+n+3 ≤ g.roles.length) :
    Last fallback (readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader
      (CompleteTranscript.step base H state).2 payload).state := by
  apply layer_last
  exact step_last_inside base H fallback state (by omega)

theorem head_setup {n assertions : ℕ} (state future : CompleteTranscript.State g fields Advice Key Base C)
    (payload : LayerPayload F n) (ids : Layered.Replay.LayerPads Pad n) (offset : ℕ)
    (fits : state.rank.val+n+3 ≤ g.roles.length)
    (extended : Extends fallback
      (readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader
        (CompleteTranscript.step base H state).2 payload).state future) :
    setupLayer (CompleteTranscript.reader side field decode nonzero base H)
      (CompleteTranscript.step base H state).2 payload
      (fun i : Fin assertions => decode (CompleteTranscript.step base H state).1 (offset+i.val)) ids =
      ⟨linearPlan ids,
        (fun i => decode (lookup fallback future (state.rank.val+1+i.val)) 0),
        nonzero (lookup fallback future (state.rank.val+1+n)),
        decode (lookup fallback future (state.rank.val+n+2)) 0,
        (fun i => decode (lookup fallback future state.rank.val) (offset+i.val))⟩ := by
  have inside : state.rank.val < g.roles.length := by omega
  have first : (CompleteTranscript.step base H state).2.rank.val = state.rank.val+1 := by
    rw [SimulationWrites.step_rank]
    exact Nat.min_eq_right (by omega)
  have layer := layer_properties_into side field base H decode nonzero fallback
    (CompleteTranscript.step base H state).2 future payload (by rw [first]; omega) extended
  have firstExtended := (layer_extends side field base H decode nonzero fallback
    (CompleteTranscript.step base H state).2 payload).trans extended
  have answer := step_answer_into base H fallback state future inside firstExtended
  simp only [setupLayer]
  rw [layer.2.1,layer.2.2.1,layer.2.2.2,answer,first]
  rw [show state.rank.val+1+n+1 = state.rank.val+n+2 by omega]

theorem readSetup_into {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit)
    (state future : CompleteTranscript.State g fields Advice Key Base C) (continuing : Bool)
    (last : continuing = true → Last fallback state)
    (positive : continuing = true → 0 < state.rank.val)
    (fits : state.rank.val+HonestTranscript.circuitFuel plan continuing ≤ g.roles.length)
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
            simp only [HonestTranscript.circuitFuel,Bool.false_eq_true,↓reduceIte] at fits
            omega
          have answer := step_answer_into base H fallback state future inside extended
          simp only [readSetup,inputCoefficients,Bool.false_eq_true,↓reduceIte,
            CompleteTranscript.reader,messagesFromSetup,replayStart,replayOffset,
            FrontendReplay.hasLayers,FrontendReplay.readFrom,Bool.false_and,Nat.zero_add]
          rw [answer]
      | true =>
          change Extends fallback state future at extended
          have value : state.lastAnswer = lookup fallback future (state.rank.val-1) :=
            (last rfl).trans (extended.2 _ (by have := positive rfl; omega)).symm
          simp only [readSetup,inputCoefficients,↓reduceIte,CompleteTranscript.reader,messagesFromSetup,
            replayStart,replayOffset,FrontendReplay.hasLayers,FrontendReplay.readFrom,
            Bool.not_false,Bool.true_and]
          rw [value]
  | @layer out mid input assertions body rest metadata tail ih =>
      let first := CompleteTranscript.step base H state
      let replay := readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader first.2 payload.1
      have headFits : state.rank.val+mid+3 ≤ g.roles.length := by
        simp only [HonestTranscript.circuitFuel] at fits
        omega
      have rank := head_rank side field base H decode nonzero state payload.1 headFits
      have rankNamed : replay.state.rank.val = state.rank.val+mid+3 := rank
      have tailFits : replay.state.rank.val+HonestTranscript.circuitFuel tail true ≤ g.roles.length := by
        rw [rank]
        simp only [HonestTranscript.circuitFuel] at fits
        omega
      have through := (readSetup_extends base H side field decode nonzero fallback
        tail ids.2 payload.2 replay.state true).trans extended
      have head := head_setup side field base H decode nonzero fallback (assertions := assertions)
        state future payload.1 ids.1 0 headFits through
      have headLast := head_last side field base H decode nonzero fallback state payload.1 headFits
      have tailEq := ih ids.2 payload.2 replay.state future true (fun _ => headLast)
        (fun _ => by rw [rank]; omega) tailFits extended
      dsimp only [readSetup,messagesFromSetup]
      apply Prod.ext
      · have message := congrArg (fun setup =>
          (messagesFromSetup (.layer assertions body rest)
            (setup,(readSetup (CompleteTranscript.reader side field decode nonzero base H)
              tail ids.2 payload.2 replay.state true).1) payload).1) head
        simpa only [first,CompleteTranscript.reader,messagesFromSetup,replayStart,replayOffset,FrontendReplay.hasLayers,
          FrontendReplay.readFrom,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte,
          linearPlan,Nat.zero_add] using message
      · cases h : FrontendReplay.hasLayers rest with
        | false =>
            simp only [replayStart,replayOffset,h,Bool.not_false,Bool.true_and,↓reduceIte] at tailEq
            rw [rankNamed,show state.rank.val+mid+3-1 = state.rank.val+mid+2 by omega] at tailEq
            simpa only [first,replay,CompleteTranscript.reader,replayStart,replayOffset,FrontendReplay.hasLayers,FrontendReplay.readFrom,h,
              Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte] using tailEq
        | true =>
            simp only [replayStart,replayOffset,h,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte] at tailEq
            rw [rankNamed] at tailEq
            simpa only [first,replay,CompleteTranscript.reader,replayStart,replayOffset,FrontendReplay.hasLayers,FrontendReplay.readFrom,h,
              Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte] using tailEq
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      let first := CompleteTranscript.step base H state
      let replay := readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader first.2 payload.1
      have headFits : state.rank.val+mid+3 ≤ g.roles.length := by
        simp only [HonestTranscript.circuitFuel] at fits
        omega
      have rank := head_rank side field base H decode nonzero state payload.1 headFits
      have rankNamed : replay.state.rank.val = state.rank.val+mid+3 := rank
      have tailFits : replay.state.rank.val+HonestTranscript.circuitFuel tail true ≤ g.roles.length := by
        rw [rank]
        simp only [HonestTranscript.circuitFuel] at fits
        omega
      have through := (readSetup_extends base H side field decode nonzero fallback
        tail ids.2 payload.2 replay.state true).trans extended
      have firstThrough := (layer_extends side field base H decode nonzero fallback first.2 payload.1).trans through
      have answer := step_answer_into base H fallback state future (by omega) firstThrough
      have head := head_setup side field base H decode nonzero fallback (assertions := assertions)
        state future payload.1 ids.1 checks headFits through
      have headLast := head_last side field base H decode nonzero fallback state payload.1 headFits
      have tailEq := ih ids.2 payload.2 replay.state future true (fun _ => headLast)
        (fun _ => by rw [rank]; omega) tailFits extended
      dsimp only [readSetup,messagesFromSetup]
      apply Prod.ext
      · simp only [CompleteTranscript.reader,replayStart,replayOffset,FrontendReplay.hasLayers,
          FrontendReplay.readFrom,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte,
          answer,Nat.zero_add]
      · apply Prod.ext
        · have message := congrArg (fun setup =>
            (messagesFromSetup (.layer assertions body rest)
              (setup,(readSetup (CompleteTranscript.reader side field decode nonzero base H)
                tail ids.2 payload.2 replay.state true).1) payload).1) head
          simpa only [first,CompleteTranscript.reader,messagesFromSetup,replayStart,replayOffset,FrontendReplay.hasLayers,
            FrontendReplay.readFrom,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte,
            linearPlan,Nat.zero_add] using message
        · cases h : FrontendReplay.hasLayers rest with
          | false =>
              simp only [replayStart,replayOffset,h,Bool.not_false,Bool.true_and,↓reduceIte] at tailEq
              rw [rankNamed,show state.rank.val+mid+3-1 = state.rank.val+mid+2 by omega] at tailEq
              simpa only [first,replay,CompleteTranscript.reader,replayStart,replayOffset,FrontendReplay.hasLayers,FrontendReplay.readFrom,h,
                Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte] using tailEq
          | true =>
              simp only [replayStart,replayOffset,h,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte] at tailEq
              rw [rankNamed] at tailEq
              simpa only [first,replay,CompleteTranscript.reader,replayStart,replayOffset,FrontendReplay.hasLayers,FrontendReplay.readFrom,h,
                Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte] using tailEq

theorem readSetup_initial_into {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit)
    (state future : CompleteTranscript.State g fields Advice Key Base C)
    (fits : state.rank.val+HonestTranscript.circuitFuel plan false ≤ g.roles.length)
    (extended : Extends fallback
      (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state false).2 future) :
    messagesFromSetup circuit
      (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state false).1 payload =
      FrontendReplay.readFrom decode nonzero circuit ids payload (lookup fallback future) state.rank.val 0 := by
  simpa only [replayStart,replayOffset,Bool.false_and,Bool.false_eq_true,↓reduceIte] using
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
      · cases h : FrontendReplay.hasLayers rest <;>
          simpa only [h,Bool.false_eq_true,↓reduceIte,Nat.add_assoc] using
            ih ids.2 payload.2 (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2)
              (if FrontendReplay.hasLayers rest then 0 else 1)

end LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape
