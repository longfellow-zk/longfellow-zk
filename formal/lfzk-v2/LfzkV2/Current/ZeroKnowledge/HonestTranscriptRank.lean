import LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdoc
import LfzkV2.Current.ZeroKnowledge.FrontendPrefix

/-! Exact counters of the honest causal program. Counters saturate at the
end of the ordinary schedule; the static frontend counts below then show
that the actual mdoc program stops at the joint backend, before saturation.
No property of the witness, messages or oracle answers enters this count. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript
open Merkle.RandomOracle SumcheckV2
open scoped Classical

variable {State Query Answer : Type}

def Counter (cap : ℕ) (rank : State → ℕ) (first last : State) (cost : ℕ) : Prop :=
  rank last = min cap (rank first+cost)

theorem Counter.rebase {cap : ℕ} {rank : State → ℕ} {first last first' last' : State} {cost : ℕ}
    (counter : Counter cap rank first last cost)
    (sameFirst : rank first' = rank first) (sameLast : rank last' = rank last) :
    Counter cap rank first' last' cost := by
  simpa only [Counter,sameFirst,sameLast] using counter

theorem Counter.bind {A B : Type} {n m cap : ℕ} {rank : State → ℕ}
    (first : Tree Query Answer A n) (next : A → Tree Query Answer B m)
    (stateA : A → State) (stateB : B → State) (initial : State) (H : Query → Answer)
    (before : Counter cap rank initial (stateA (first.run H).1) n)
    (after : ∀ a, Counter cap rank (stateA a) (stateB ((next a).run H).1) m) :
    Counter cap rank initial (stateB ((first.bind next).run H).1) (m+n) := by
  rw [Tree.run_bind]
  have later := after (first.run H).1
  simp only [Counter] at before later ⊢
  omega

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

set_option backward.isDefEq.respectTransparency false in
theorem circuit_counter (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (w : Cube input → F) (weights : Cube out → F) (state : State)
    (pads : Frontend.CircuitTape body) (continuing : Bool) (H : Point → Digest × C) :
    Counter g.roles.length (fun state : State => state.rank.val) state
      ((circuit (complete base side field decode nonzero) plan ids w weights state pads continuing).run H).1.state
      (circuitFuel plan continuing) := by
  rw [circuit_output]
  simp only [complete_reader]
  unfold Counter
  rw [Frontend.Prefix.circuit_state]
  dsimp only
  rw [execute_counter,circuit_length]

end Complete
end LfzkV2.Current.ZeroKnowledge.HonestTranscript
