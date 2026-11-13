import LfzkV2.Current.ZeroKnowledge.FrontendPrefix

/-! Static frontend schedule lengths and actual prefix counters. No alternate
honest-prover interpreter or whole-answer finalization is constructed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.ScheduleLength
open Merkle.RandomOracle SumcheckV2
open scoped Classical
section Static
variable {F : Type} [Field F]
def circuitFuel : {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    FrontendSchedule.Plan F circuit → Bool → ℕ
  | _,_,_,.input,continuing => if continuing then 0 else 1
  | _,_,_,.inputEntry ..,continuing => if continuing then 0 else 1
  | _,_,_,.layer (mid := mid) _ tail,_ => circuitFuel tail true+(2+mid)+1
  | _,_,_,.entryLayer (mid := mid) _ _ _ tail,_ => circuitFuel tail true+(2+mid)+1


end Static
variable {State : Type}
def Counter (cap : ℕ) (rank : State → ℕ) (first last : State) (cost : ℕ) : Prop :=
  rank last = min cap (rank first+cost)


section Step
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
local notation "State" => Frontend.CompleteTranscript.State g fields Advice Key Base C
local notation "Point" => Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)

/-- This is the exact existing complete-transcript step as a bounded tree.
The exhausted branch is the reader's existing total fallback, not a query. -/
def step (state : State) : Tree Point (Digest × C) (C × State) 1 :=
  if inside : state.rank.val < g.roles.length then
    .query (Frontend.CompleteTranscript.query base state inside) fun answer =>
      .done (answer.2,Frontend.CompleteTranscript.advance base state inside answer)
  else .done (state.lastAnswer,state)

theorem step_output (state : State) (H : Point → Digest × C) :
    ((step base state).run H).1 = Frontend.CompleteTranscript.step base H state := by
  by_cases inside : state.rank.val < g.roles.length
  · simp only [step,Frontend.CompleteTranscript.step,dif_pos inside,Tree.run_query,Tree.run_done]
  · simp only [step,Frontend.CompleteTranscript.step,dif_neg inside,Tree.run_done]


end Step
section Complete
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
local notation "State" => Frontend.CompleteTranscript.State g fields Advice Key Base C
local notation "Point" => Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)

theorem step_counter (state : State) (H : Point → Digest × C) :
    Counter g.roles.length (fun state : State => state.rank.val) state ((step base state).run H).1.2 1 := by
  rw [step_output]
  unfold Frontend.CompleteTranscript.step
  split_ifs with inside
  · change state.rank.val+1 = min g.roles.length (state.rank.val+1)
    omega
  · change state.rank.val = min g.roles.length (state.rank.val+1)
    have bound := state.rank.isLt
    omega

variable {F Pad : Type} [Field F]
variable (side : Side) (field : fields side ≃ F)

omit [Field F] in
theorem execute_counter (state : State) (messages : List (Option (Layered.Replay.Message F)))
    (H : Point → Digest × C) :
    (Frontend.Prefix.execute side field base H state messages).rank.val =
      min g.roles.length (state.rank.val+messages.length) := by
  induction messages generalizing state with
  | nil =>
      change state.rank.val = min g.roles.length (state.rank.val+0)
      have bound := state.rank.isLt
      omega
  | cons message tail ih =>
      rw [Frontend.Prefix.execute,ih]
      have next := step_counter base (Frontend.Prefix.prepare side field state message) H
      rw [step_output] at next
      have prepared : (Frontend.Prefix.prepare side field state message).rank.val = state.rank.val := by
        cases message <;> rfl
      simp only [Counter,prepared] at next
      simp only [List.length_cons]
      omega

omit [Field F] in
theorem circuit_length {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (payload : Layered.Replay.Payload body) (continuing : Bool) :
    (Frontend.Prefix.circuit plan payload continuing).length = circuitFuel plan continuing := by
  induction plan generalizing continuing with
  | input => cases continuing <;> rfl
  | inputEntry => cases continuing <;> rfl
  | layer _ tail ih =>
      simp only [Frontend.Prefix.circuit,Frontend.Prefix.layer,Frontend.Prefix.rounds,circuitFuel,
        List.length_cons,List.length_append,List.length_ofFn,ih,List.length_nil]
      omega
  | entryLayer _ _ _ tail ih =>
      simp only [Frontend.Prefix.circuit,Frontend.Prefix.layer,Frontend.Prefix.rounds,circuitFuel,
        List.length_cons,List.length_append,List.length_ofFn,ih,List.length_nil]
      omega

omit [Field F] in
theorem circuitFuel_slots {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (continuing : Bool) :
    circuitFuel plan continuing = if FrontendReplay.hasLayers body then FrontendReplay.slots body
      else if continuing then 0 else 1 := by
  induction plan generalizing continuing with
  | input => cases continuing <;> rfl
  | inputEntry => cases continuing <;> rfl
  | @layer out mid input assertions body rest metadata tail ih =>
      simp only [circuitFuel,FrontendReplay.hasLayers,↓reduceIte,FrontendReplay.slots,ih]
      cases FrontendReplay.hasLayers rest <;> omega
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      simp only [circuitFuel,FrontendReplay.hasLayers,↓reduceIte,FrontendReplay.slots,ih]
      cases FrontendReplay.hasLayers rest <;> omega

omit [Field F] in
theorem circuitFuel_roles {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (side : Side) :
    circuitFuel plan false = (plan.frontend.roles side).length := by
  rw [circuitFuel_slots,← plan.slots_eq_roles_length side]
  cases h : FrontendReplay.hasLayers body
  · rw [FrontendReplay.slots_eq,h]
    rfl
  · rfl


end Complete
end LfzkV2.Current.ZeroKnowledge.Frontend.ScheduleLength
