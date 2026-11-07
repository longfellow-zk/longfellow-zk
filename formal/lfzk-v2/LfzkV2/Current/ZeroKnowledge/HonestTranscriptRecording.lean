import LfzkV2.Current.ZeroKnowledge.HonestTranscriptProgress

/-! Every actual causal query is recorded in the returned transcript
history. This is stronger than a counter bound: the complete query-key list
is identified, so an arbitrary same-rank point cannot be substituted when
proving canonical-query agreement. Local writes preserve this history. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript
open Merkle.RandomOracle SumcheckV2
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {State Query Answer : Type}

def RunRecords (log : State → List Query) (first last : State) (trace : List (Query × Answer)) : Prop :=
  log last = log first ++ trace.map Prod.fst

theorem RunRecords.refl (log : State → List Query) (state : State) :
    RunRecords (Answer := Answer) log state state [] := by simp only [RunRecords,List.map_nil,List.append_nil]

theorem RunRecords.of_log_eq (log : State → List Query) (first last : State)
    (same : log last = log first) : RunRecords (Answer := Answer) log first last [] := by
  simpa only [RunRecords,List.map_nil,List.append_nil] using same

theorem RunRecords.trans {log : State → List Query} {first middle last : State}
    {before after : List (Query × Answer)}
    (one : RunRecords log first middle before) (two : RunRecords log middle last after) :
    RunRecords log first last (before++after) := by
  simp only [RunRecords] at one two ⊢
  rw [two,one,List.map_append,List.append_assoc]

theorem RunRecords.rebase {log : State → List Query} {first last first' last' : State} {trace : List (Query × Answer)}
    (recorded : RunRecords log first last trace) (sameFirst : log first' = log first) (sameLast : log last' = log last) :
    RunRecords log first' last' trace := by simpa only [RunRecords,sameFirst,sameLast] using recorded

theorem RunRecords.bind {A B : Type} {n m : ℕ} (log : State → List Query)
    (first : Tree Query Answer A n) (next : A → Tree Query Answer B m)
    (stateA : A → State) (stateB : B → State) (initial : State) (H : Query → Answer)
    (before : RunRecords log initial (stateA (first.run H).1) (first.run H).2)
    (after : ∀ a, RunRecords log (stateA a) (stateB ((next a).run H).1) ((next a).run H).2) :
    RunRecords log initial (stateB ((first.bind next).run H).1) ((first.bind next).run H).2 := by
  rw [Tree.run_bind]
  exact before.trans (after _)

theorem RunRecords.mem {log : State → List Query} {first last : State} {trace : List (Query × Answer)}
    (recorded : RunRecords log first last trace) (qa : Query × Answer) (member : qa ∈ trace) : qa.1 ∈ log last := by
  rw [RunRecords] at recorded
  rw [recorded]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨qa,member,rfl⟩)

structure QueriesRecorded {F : Type} [Field F] (queries : Queries F State Query Answer) (log : State → List Query) : Prop where
  round : ∀ state message H, RunRecords log state (((queries.round state message).run H).1.2) ((queries.round state message).run H).2
  terminal : ∀ state message H, RunRecords log state (((queries.terminal state message).run H).1.2) ((queries.terminal state message).run H).2
  combine : ∀ state message H, RunRecords log state (((queries.combine state message).run H).1.2) ((queries.combine state message).run H).2
  assertions : ∀ state count H, RunRecords log state (((queries.assertions state count).run H).1.2) ((queries.assertions state count).run H).2
  inputAssertions : ∀ state count, log (queries.inputAssertions state count).2 = log state

section Complete
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
local notation "State" => Frontend.CompleteTranscript.State g fields Advice Key Base C
local notation "Point" => Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)

def queryLog (state : State) : List Point :=
  List.ofFn (Input.historyPoints state.rank.val (by have := state.rank.isLt; omega) state.history)

/-- The recorded list consists of the actual ancestors of the current key,
including all cached physical blocks. -/
theorem queryLog_mem_prior (state : State) (inside : state.rank.val < g.roles.length)
    (point : Point) (member : point ∈ queryLog state) :
    ∃ i : Fin (Frontend.CompleteTranscript.query base state inside).rank,
      point = (Frontend.CompleteTranscript.query base state inside).priorPoints i := by
  obtain ⟨i,same⟩ := List.mem_ofFn.mp member
  exact ⟨i,same.symm⟩

theorem advance_log (state : State) (inside : state.rank.val < g.roles.length) (answer : Digest × C) :
    queryLog (Authentication := Authentication) (Frontend.CompleteTranscript.advance base state inside answer) =
      queryLog state ++ [Frontend.CompleteTranscript.query base state inside] := by
  simp only [queryLog,Frontend.CompleteTranscript.advance,Input.historyPoints,List.ofFn_succ',
    Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append]
  rfl

theorem step_recorded (state : State) (H : Point → Digest × C) :
    RunRecords queryLog state ((step base state).run H).1.2 ((step base state).run H).2 := by
  by_cases inside : state.rank.val < g.roles.length
  · simp only [step,dif_pos inside,Tree.run_query,Tree.run_done,RunRecords,List.map_cons,List.map_nil]
    exact advance_log base state inside _
  · simp only [step,dif_neg inside,Tree.run_done]
    exact RunRecords.refl _ _

theorem complete_recorded {F : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) :
    QueriesRecorded (complete (Authentication := Authentication) (Key := Key) base side field decode nonzero) queryLog := by
  constructor
  · intro state message H
    simpa only [complete,Tree.run_map] using
      (step_recorded base (Frontend.CompleteTranscript.frontend side state
        (Frontend.CompleteTranscript.mapMessage field.symm (.round message))) H).rebase
        (first' := state) rfl rfl
  · intro state message H
    simpa only [complete,Tree.run_map] using
      (step_recorded base (Frontend.CompleteTranscript.frontend side state
        (Frontend.CompleteTranscript.mapMessage field.symm (.cross message))) H).rebase
        (first' := state) rfl rfl
  · intro state message H
    simpa only [complete,Tree.run_map] using
      (step_recorded base (Frontend.CompleteTranscript.frontend side state
        (Frontend.CompleteTranscript.mapMessage field.symm (.claims message.1 message.2))) H).rebase
        (first' := state) rfl rfl
  · intro state count H
    simpa only [complete,Tree.run_map] using step_recorded base state H
  · intro state count
    rfl
end Complete

section Frontend
variable {F Pad : Type} [Field F]
variable (queries : Queries F State Query Answer) (log : State → List Query) (recorded : QueriesRecorded queries log)

include recorded in
theorem rounds_recorded {n : ℕ} (q w : Cube n → F) (state : State) (pads : Fin n → RoundPoly F) (H : Query → Answer) :
    RunRecords log state ((rounds queries q w state pads).run H).1.state ((rounds queries q w state pads).run H).2 := by
  induction n generalizing state with
  | zero => exact RunRecords.refl _ _
  | succ n ih =>
      simp only [rounds,Tree.run_bind,Tree.run_map]
      exact (recorded.round state _ H).trans (ih _ _ _ _)

include recorded in
theorem layer_recorded {n : ℕ} (q w : Cube n → F) (state : State) (pads : Frontend.LayerTape F n) (H : Query → Answer) :
    RunRecords log state ((layer queries q w state pads).run H).1.read.state ((layer queries q w state pads).run H).2 := by
  simp only [layer,Tree.run_bind,Tree.run_map]
  exact (rounds_recorded queries log recorded q w state pads.1 H).trans
    ((recorded.terminal _ _ H).trans (recorded.combine _ _ H))

include recorded in
theorem circuit_recorded {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (w : Cube input → F) (weights : Cube out → F) (state : State) (pads : Frontend.CircuitTape body)
    (continuing : Bool) (H : Query → Answer) :
    RunRecords log state ((circuit queries plan ids w weights state pads continuing).run H).1.state
      ((circuit queries plan ids w weights state pads continuing).run H).2 := by
  induction plan generalizing state continuing with
  | input =>
      cases continuing
      · dsimp only [circuit,circuitFuel]; rw [Tree.run_map]; exact recorded.assertions _ _ _
      · exact RunRecords.refl _ _
  | inputEntry entry empty =>
      cases continuing
      · dsimp only [circuit,circuitFuel]; rw [Tree.run_map]; exact recorded.assertions _ _ _
      · exact RunRecords.of_log_eq _ _ _ (recorded.inputAssertions _ _)
  | layer h tail ih =>
      dsimp only [circuit,circuitFuel]
      rw [Tree.run_bind,Tree.run_bind,Tree.run_map]
      exact (recorded.assertions _ _ H).trans
        ((layer_recorded queries log recorded _ _ _ _ H).trans (ih _ _ _ _ _ true))
  | entryLayer h entry empty tail ih =>
      dsimp only [circuit,circuitFuel]
      rw [Tree.run_bind,Tree.run_bind,Tree.run_map]
      exact (recorded.assertions _ _ H).trans
        ((layer_recorded queries log recorded _ _ _ _ H).trans (ih _ _ _ _ _ true))
end Frontend
end LfzkV2.Current.ZeroKnowledge.HonestTranscript
