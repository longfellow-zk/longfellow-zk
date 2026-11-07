import LfzkV2.Current.ZeroKnowledge.FrontendCompleteTranscript
import Merkle.TreeCompose

/-! Oracle-query actions for the honest frontend. Arithmetic chooses a
message before an action is run. The action queries the current chained key
once and passes its actual answer to the existing reader; it has no oracle
argument while constructing that message. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript
open Merkle.RandomOracle SumcheckV2
open scoped Classical

structure Queries (F State Query Answer : Type) [Field F] where
  round : State → RoundPoly F → Tree Query Answer (F × State) 1
  terminal : State → F → Tree Query Answer ({r : F // r ≠ 0} × State) 1
  combine : State → F × F → Tree Query Answer (F × State) 1
  assertions : State → (count : ℕ) → Tree Query Answer ((Fin count → F) × State) 1
  inputAssertions : State → (count : ℕ) → (Fin count → F) × State

def Queries.reader {F State Query Answer : Type} [Field F]
    (queries : Queries F State Query Answer) (H : Query → Answer) : Frontend.CircuitReader F State where
  round state message := ((queries.round state message).run H).1
  terminal state message := ((queries.terminal state message).run H).1
  combine state message := ((queries.combine state message).run H).1
  assertions state count := ((queries.assertions state count).run H).1
  inputAssertions := queries.inputAssertions

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

def complete {F : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) :
    Queries F State Point (Digest × C) where
  round state polynomial :=
    (step base (Frontend.CompleteTranscript.frontend side state
      (Frontend.CompleteTranscript.mapMessage field.symm (.round polynomial)))).map fun answer =>
        (decode answer.1 0,answer.2)
  terminal state cross :=
    (step base (Frontend.CompleteTranscript.frontend side state
      (Frontend.CompleteTranscript.mapMessage field.symm (.cross cross)))).map fun answer =>
        (nonzero answer.1,answer.2)
  combine state factors :=
    (step base (Frontend.CompleteTranscript.frontend side state
      (Frontend.CompleteTranscript.mapMessage field.symm (.claims factors.1 factors.2)))).map fun answer =>
        (decode answer.1 0,answer.2)
  assertions state count :=
    (step base state).map fun answer => (fun i : Fin count => decode answer.1 i.val,answer.2)
  inputAssertions state count := (fun i : Fin count => decode state.lastAnswer (1+i.val),state)

/-- The tree actions instantiate the actual body-free runtime reader, not
a supplied oracle-compliance or transcript-equivalence certificate. -/
theorem complete_reader {F : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (H : Point → Digest × C) :
    (complete base side field decode nonzero).reader H =
      Frontend.CompleteTranscript.reader side field decode nonzero base H := by
  simp only [Queries.reader,complete,Tree.run_map,step_output,Frontend.CompleteTranscript.reader]

end LfzkV2.Current.ZeroKnowledge.HonestTranscript
