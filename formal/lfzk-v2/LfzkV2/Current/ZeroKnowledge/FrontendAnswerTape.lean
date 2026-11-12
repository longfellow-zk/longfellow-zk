import LfzkV2.Current.ZeroKnowledge.FrontendSimulationWrites

/-! Challenge readback from the generated state. Every boundary stores the
whole answer it just used. Later boundaries append answers and preserve all
earlier coordinates, including the final combine answer reused by input
assertions. No challenge is reconstructed from a prover message. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape

open SumcheckV2
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)

def lookup (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C) (index : ℕ) : C :=
  if inside : index < state.rank.val then state.past ⟨index,inside⟩ else fallback

def pointLookup (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
    (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
    (fallback : C)
    (point : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base)) (index : ℕ) : C :=
  if inside : index < point.rank then point.priorAnswers H ⟨index,inside⟩ else fallback

theorem query_lookup (fallback : C) (context : Key)
    (state : CompleteTranscript.State g fields Advice Key Base C) (inside : state.rank.val < g.roles.length)
    (good : History.Good base H context state) :
    lookup fallback state = pointLookup H fallback (CompleteTranscript.query base state inside) := by
  funext index
  by_cases prior : index < state.rank.val
  · simp only [lookup,pointLookup,CompleteTranscript.query,Input.rank,dif_pos prior]
    exact congrFun (History.query_past base H context state inside good) ⟨index,prior⟩
  · simp only [lookup,pointLookup,CompleteTranscript.query,Input.rank,dif_neg prior]

theorem answerTape_point (fallback : C)
    (point : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base)) (origin index : ℕ) :
    ApplicationPrefix.answerTape point (point.priorAnswers H) fallback origin index =
      pointLookup H fallback point (origin+index) := by
  by_cases inside : origin+index < point.rank <;>
    simp only [ApplicationPrefix.answerTape,ApplicationPrefix.strictAnswer,pointLookup,inside,
      ↓reduceDIte,Option.getD_some,Option.getD_none]

theorem frontend_read {F Pad : Type} [Field F] (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    (fallback : C) {out input : ℕ} (circuit : Layered.Circuit F out input)
    (ids : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (point : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base)) (origin : ℕ) :
    FrontendReplay.read decode nonzero circuit ids payload
      (ApplicationPrefix.frontendTape point (point.priorAnswers H) fallback origin (FrontendReplay.slots circuit)) =
        FrontendReplay.read decode nonzero circuit ids payload (fun q => pointLookup H fallback point (origin+q)) := by
  rw [ApplicationPrefix.read_frontendTape]
  exact congrArg (FrontendReplay.read decode nonzero circuit ids payload)
    (funext fun q => answerTape_point H fallback point origin q)

def Extends (fallback : C) (first last : CompleteTranscript.State g fields Advice Key Base C) : Prop :=
  first.rank.val ≤ last.rank.val ∧ ∀ index < first.rank.val, lookup fallback last index = lookup fallback first index

theorem Extends.refl (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C) :
    Extends fallback state state := ⟨le_rfl,fun _ _ => rfl⟩

theorem Extends.trans {fallback : C} {first middle last : CompleteTranscript.State g fields Advice Key Base C}
    (before : Extends fallback first middle) (after : Extends fallback middle last) :
    Extends fallback first last :=
  ⟨before.1.trans after.1,fun index inside => (after.2 index (inside.trans_le before.1)).trans (before.2 index inside)⟩

theorem advance_at (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) (answer : Digest × C) :
    lookup fallback (CompleteTranscript.advance base state inside answer) state.rank.val = answer.2 := by
  simp only [lookup,CompleteTranscript.advance,Nat.lt_succ_self,↓reduceDIte]
  exact Fin.snoc_last _ _

theorem advance_extends (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) (answer : Digest × C) :
    Extends fallback state (CompleteTranscript.advance base state inside answer) := by
  refine ⟨by change state.rank.val ≤ state.rank.val+1; omega,?_⟩
  intro index prior
  have after : index < state.rank.val+1 := by omega
  simp only [lookup,CompleteTranscript.advance,dif_pos prior,dif_pos after]
  exact Fin.snoc_castSucc (α := fun _ : Fin (state.rank.val+1) => C) answer.2 state.past ⟨index,prior⟩

theorem step_extends (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C) :
    Extends fallback state (CompleteTranscript.step base H state).2 := by
  by_cases inside : state.rank.val < g.roles.length
  · rw [CompleteTranscript.step_query base H state inside]
    exact advance_extends base fallback state inside _
  · simpa only [CompleteTranscript.step,dif_neg inside] using Extends.refl fallback state

theorem step_answer (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) :
    (CompleteTranscript.step base H state).1 =
      lookup fallback (CompleteTranscript.step base H state).2 state.rank.val := by
  rw [CompleteTranscript.step_query base H state inside]
  exact (advance_at base fallback state inside _).symm

theorem step_answer_into (fallback : C) (state future : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length)
    (extended : Extends fallback (CompleteTranscript.step base H state).2 future) :
    (CompleteTranscript.step base H state).1 = lookup fallback future state.rank.val := by
  have prior : state.rank.val < (CompleteTranscript.step base H state).2.rank.val := by
    rw [CompleteTranscript.step_query base H state inside]
    change state.rank.val < state.rank.val+1
    omega
  exact (step_answer base H fallback state inside).trans (extended.2 _ prior).symm

def Last (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C) : Prop :=
  state.lastAnswer = lookup fallback state (state.rank.val-1)

theorem initial_last (context : Key) (fallback : C) :
    Last (g := g) (fields := fields) (Advice := Advice) (Base := Base) fallback
      (CompleteTranscript.initial context fallback) := rfl

theorem advance_last (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) (answer : Digest × C) :
    Last fallback (CompleteTranscript.advance base state inside answer) := by
  change answer.2 = lookup fallback (CompleteTranscript.advance base state inside answer) (state.rank.val+1-1)
  rw [Nat.add_sub_cancel]
  exact (advance_at base fallback state inside answer).symm

theorem step_last_inside (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) : Last fallback (CompleteTranscript.step base H state).2 := by
  rw [CompleteTranscript.step_query base H state inside]
  exact advance_last base fallback state inside _

theorem step_last (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (last : Last fallback state) : Last fallback (CompleteTranscript.step base H state).2 := by
  by_cases inside : state.rank.val < g.roles.length
  · rw [CompleteTranscript.step_query base H state inside]
    exact advance_last base fallback state inside _
  · simpa only [CompleteTranscript.step,dif_neg inside] using last

theorem bind_last (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (write : ProtocolWrites.Fresh g fields Advice → ProtocolWrites.Fresh g fields Advice)
    (last : Last fallback state) : Last fallback (CompleteTranscript.bind state write) := last

theorem bind_extends (fallback : C) (state : CompleteTranscript.State g fields Advice Key Base C)
    (write : ProtocolWrites.Fresh g fields Advice → ProtocolWrites.Fresh g fields Advice) :
    Extends fallback state (CompleteTranscript.bind state write) := Extends.refl fallback state

theorem execute_extends {F : Type} (side : Side) (field : fields side ≃ F) (fallback : C)
    (state : CompleteTranscript.State g fields Advice Key Base C)
    (messages : List (Option (Layered.Replay.Message F))) :
    Extends fallback state (Prefix.execute side field base H state messages) := by
  induction messages generalizing state with
  | nil => exact Extends.refl fallback state
  | cons message tail ih =>
      have prepared : Extends fallback state (Prefix.prepare side field state message) := by
        cases message with
        | none => exact Extends.refl fallback state
        | some message => exact bind_extends fallback state _
      exact prepared.trans ((step_extends base H fallback _).trans (ih _))

theorem execute_last {F : Type} (side : Side) (field : fields side ≃ F) (fallback : C)
    (state : CompleteTranscript.State g fields Advice Key Base C)
    (messages : List (Option (Layered.Replay.Message F))) (last : Last fallback state) :
    Last fallback (Prefix.execute side field base H state messages) := by
  induction messages generalizing state with
  | nil => exact last
  | cons message tail ih =>
      apply ih
      apply step_last
      cases message with
      | none => exact last
      | some message => exact bind_last fallback state _ last

theorem rounds_extends {F : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (fallback : C)
    {n : ℕ} (state : CompleteTranscript.State g fields Advice Key Base C) (messages : Fin n → RoundPoly F) :
    Extends fallback state
      (readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader state messages).2 := by
  rw [Prefix.rounds_state]
  exact execute_extends base H side field fallback state _

theorem rounds_point {F : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (fallback : C)
    {n : ℕ} (state : CompleteTranscript.State g fields Advice Key Base C) (messages : Fin n → RoundPoly F)
    (fits : state.rank.val+n ≤ g.roles.length) :
    (readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader state messages).1 =
      fun i => decode (lookup fallback
        (readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader state messages).2
          (state.rank.val+i.val)) 0 := by
  induction n generalizing state with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      let pending := CompleteTranscript.frontend side state
        (CompleteTranscript.mapMessage field.symm (.round (messages 0)))
      let answer := CompleteTranscript.step base H pending
      have inside : pending.rank.val < g.roles.length := by
        change state.rank.val < g.roles.length
        omega
      have nextRank : answer.2.rank.val = state.rank.val+1 := by
        rw [SimulationWrites.step_rank]
        exact Nat.min_eq_right (by change state.rank.val+1 ≤ g.roles.length; omega)
      have tailFits : answer.2.rank.val+n ≤ g.roles.length := by rw [nextRank]; omega
      have tailEq := ih answer.2 (fun i : Fin n => messages i.succ) tailFits
      have extended := rounds_extends base H side field decode nonzero fallback
        answer.2 (fun i : Fin n => messages i.succ)
      have firstInside : state.rank.val < answer.2.rank.val := by rw [nextRank]; omega
      have first := step_answer base H fallback pending inside
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change decode answer.1 0 = decode (lookup fallback
          (readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader answer.2
            (fun i : Fin n => messages i.succ)).2 (state.rank.val+0)) 0
        rw [Nat.add_zero]
        exact congrArg (fun value => decode value 0) (first.trans (extended.2 _ firstInside).symm)
      · change (readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader answer.2
          (fun i : Fin n => messages i.succ)).1 j =
            decode (lookup fallback
              (readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader answer.2
                (fun i : Fin n => messages i.succ)).2 (state.rank.val+j.succ.val)) 0
        simpa only [nextRank,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1 j.val] using congrFun tailEq j

theorem readSetup_extends {F Pad : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (fallback : C)
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit) (state : CompleteTranscript.State g fields Advice Key Base C)
    (continuing : Bool) :
    Extends fallback state (readSetup (CompleteTranscript.reader side field decode nonzero base H)
      plan ids payload state continuing).2 := by
  rw [Prefix.circuit_state]
  exact execute_extends base H side field fallback state _

end LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape
