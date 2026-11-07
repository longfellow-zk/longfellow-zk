import LfzkV2.Current.ZeroKnowledge.HonestTranscriptCircuit

/-! Structural query causality of the honest frontend tree. Each real
boundary queries its current rank and advances that rank; local arithmetic
and input-assertion reads do not advance it. Consequently every query in a
completed prefix has smaller rank than the returned state. This fact is
derived for the actual complete-transcript actions, not assumed as a
whole-program oracle-compliance certificate. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript
open Merkle.RandomOracle SumcheckV2
open scoped Classical

variable {State Query Answer : Type}

def RunProgress (rank : State → ℕ) (queryRank : Query → ℕ)
    (first last : State) (trace : List (Query × Answer)) : Prop :=
  rank first ≤ rank last ∧ ∀ qa ∈ trace, queryRank qa.1 < rank last

theorem RunProgress.refl (rank : State → ℕ) (queryRank : Query → ℕ) (state : State) :
    RunProgress (Answer := Answer) rank queryRank state state [] := by
  exact ⟨le_refl _,fun _ h => nomatch h⟩

theorem RunProgress.of_rank_eq (rank : State → ℕ) (queryRank : Query → ℕ) (first last : State)
    (equal : rank last = rank first) : RunProgress (Answer := Answer) rank queryRank first last [] := by
  exact ⟨le_of_eq equal.symm,fun _ h => nomatch h⟩

theorem RunProgress.trans {rank : State → ℕ} {queryRank : Query → ℕ}
    {first middle last : State} {before after : List (Query × Answer)}
    (hfirst : RunProgress rank queryRank first middle before)
    (hsecond : RunProgress rank queryRank middle last after) :
    RunProgress rank queryRank first last (before++after) := by
  refine ⟨hfirst.1.trans hsecond.1,?_⟩
  intro qa member
  rcases List.mem_append.mp member with member | member
  · exact (hfirst.2 qa member).trans_le hsecond.1
  · exact hsecond.2 qa member

/-- Local writes may change a state without changing its query counter. -/
theorem RunProgress.of_ranks {rank : State → ℕ} {queryRank : Query → ℕ}
    {first last first' last' : State} {trace : List (Query × Answer)}
    (sameFirst : rank first' = rank first) (sameLast : rank last' = rank last)
    (progress : RunProgress rank queryRank first last trace) : RunProgress rank queryRank first' last' trace := by
  simpa only [RunProgress,sameFirst,sameLast] using progress

theorem RunProgress.rebase {rank : State → ℕ} {queryRank : Query → ℕ}
    {first last first' last' : State} {trace : List (Query × Answer)}
    (progress : RunProgress rank queryRank first last trace)
    (sameFirst : rank first' = rank first) (sameLast : rank last' = rank last) :
    RunProgress rank queryRank first' last' trace := of_ranks sameFirst sameLast progress

/-- Sequential causal computations compose without inspecting their local
arithmetic or expanding the returned state. -/
theorem RunProgress.bind {A B : Type} {n m : ℕ}
    {rank : State → ℕ} {queryRank : Query → ℕ}
    (first : Tree Query Answer A n) (next : A → Tree Query Answer B m)
    (stateA : A → State) (stateB : B → State) (initial : State) (H : Query → Answer)
    (before : RunProgress rank queryRank initial (stateA (first.run H).1) (first.run H).2)
    (after : ∀ a, RunProgress rank queryRank (stateA a) (stateB ((next a).run H).1)
      ((next a).run H).2) :
    RunProgress rank queryRank initial (stateB ((first.bind next).run H).1)
      ((first.bind next).run H).2 := by
  rw [Tree.run_bind]
  exact before.trans (after _)

structure QueriesProgress {F : Type} [Field F] (queries : Queries F State Query Answer)
    (rank : State → ℕ) (queryRank : Query → ℕ) : Prop where
  round : ∀ state message H, RunProgress rank queryRank state
    (((queries.round state message).run H).1.2) ((queries.round state message).run H).2
  terminal : ∀ state message H, RunProgress rank queryRank state
    (((queries.terminal state message).run H).1.2) ((queries.terminal state message).run H).2
  combine : ∀ state message H, RunProgress rank queryRank state
    (((queries.combine state message).run H).1.2) ((queries.combine state message).run H).2
  assertions : ∀ state count H, RunProgress rank queryRank state
    (((queries.assertions state count).run H).1.2) ((queries.assertions state count).run H).2
  inputAssertions : ∀ state count, rank (queries.inputAssertions state count).2 = rank state

section Complete
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
local notation "State" => Frontend.CompleteTranscript.State g fields Advice Key Base C
local notation "Point" => Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)

theorem step_progress (state : State) (H : Point → Digest × C) :
    RunProgress (fun state : State => state.rank.val) Input.rank state
      ((step base state).run H).1.2 ((step base state).run H).2 := by
  by_cases inside : state.rank.val < g.roles.length
  · simp only [step,dif_pos inside,Tree.run_query,Tree.run_done,RunProgress]
    constructor
    · change state.rank.val ≤ state.rank.val+1
      omega
    · intro qa member
      have same := List.mem_singleton.mp member
      subst qa
      change state.rank.val < state.rank.val+1
      omega
  · simp only [step,dif_neg inside,Tree.run_done]
    exact RunProgress.refl _ _ _

theorem complete_progress {F : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) :
    QueriesProgress (complete (Authentication := Authentication) base side field decode nonzero)
      (fun state : State => state.rank.val) Input.rank := by
  constructor
  · intro state message H
    simpa only [complete,Tree.run_map,Frontend.CompleteTranscript.frontend,Frontend.CompleteTranscript.bind,RunProgress]
      using step_progress base (Frontend.CompleteTranscript.frontend side state
        (Frontend.CompleteTranscript.mapMessage field.symm (.round message))) H
  · intro state message H
    simpa only [complete,Tree.run_map,Frontend.CompleteTranscript.frontend,Frontend.CompleteTranscript.bind,RunProgress]
      using step_progress base (Frontend.CompleteTranscript.frontend side state
        (Frontend.CompleteTranscript.mapMessage field.symm (.cross message))) H
  · intro state message H
    simpa only [complete,Tree.run_map,Frontend.CompleteTranscript.frontend,Frontend.CompleteTranscript.bind,RunProgress]
      using step_progress base (Frontend.CompleteTranscript.frontend side state
        (Frontend.CompleteTranscript.mapMessage field.symm (.claims message.1 message.2))) H
  · intro state count H
    simpa only [complete,Tree.run_map] using step_progress base state H
  · intro state count
    rfl
end Complete

section Frontend
variable {F Pad : Type} [Field F]
variable (queries : Queries F State Query Answer) (rank : State → ℕ) (queryRank : Query → ℕ)
variable (progress : QueriesProgress queries rank queryRank)

include progress in
theorem rounds_progress {n : ℕ} (q w : Cube n → F) (state : State)
    (pads : Fin n → RoundPoly F) (H : Query → Answer) :
    RunProgress rank queryRank state ((rounds queries q w state pads).run H).1.state
      ((rounds queries q w state pads).run H).2 := by
  induction n generalizing state with
  | zero => exact RunProgress.refl _ _ _
  | succ n ih =>
      simp only [rounds,Tree.run_bind,Tree.run_map]
      exact (progress.round state _ H).trans (ih _ _ _ _)

include progress in
theorem layer_progress {n : ℕ} (q w : Cube n → F) (state : State)
    (pads : Frontend.LayerTape F n) (H : Query → Answer) :
    RunProgress rank queryRank state ((layer queries q w state pads).run H).1.read.state
      ((layer queries q w state pads).run H).2 := by
  simp only [layer,Tree.run_bind,Tree.run_map]
  exact (rounds_progress queries rank queryRank progress q w state pads.1 H).trans
    ((progress.terminal _ _ H).trans (progress.combine _ _ H))

include progress in
set_option backward.isDefEq.respectTransparency false in
theorem circuit_progress {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (w : Cube input → F) (weights : Cube out → F) (state : State)
    (pads : Frontend.CircuitTape body) (continuing : Bool) (H : Query → Answer) :
    RunProgress rank queryRank state ((circuit queries plan ids w weights state pads continuing).run H).1.state
      ((circuit queries plan ids w weights state pads continuing).run H).2 := by
  induction plan generalizing state continuing with
  | input =>
      cases continuing
      · dsimp only [circuit,circuitFuel]
        rw [Tree.run_map]
        exact progress.assertions _ _ _
      · exact RunProgress.refl _ _ _
  | inputEntry entry empty =>
      cases continuing
      · dsimp only [circuit,circuitFuel]
        rw [Tree.run_map]
        exact progress.assertions _ _ _
      · exact RunProgress.of_rank_eq _ _ _ _ (progress.inputAssertions _ _)
  | layer h tail ih =>
      dsimp only [circuit,circuitFuel]
      rw [Tree.run_bind,Tree.run_bind,Tree.run_map]
      exact (progress.assertions _ _ H).trans
        ((layer_progress queries rank queryRank progress _ _ _ _ H).trans (ih _ _ _ _ _ true))
  | entryLayer h entry empty tail ih =>
      dsimp only [circuit,circuitFuel]
      rw [Tree.run_bind,Tree.run_bind,Tree.run_map]
      exact (progress.assertions _ _ H).trans
        ((layer_progress queries rank queryRank progress _ _ _ _ H).trans (ih _ _ _ _ _ true))

end Frontend
end LfzkV2.Current.ZeroKnowledge.HonestTranscript
