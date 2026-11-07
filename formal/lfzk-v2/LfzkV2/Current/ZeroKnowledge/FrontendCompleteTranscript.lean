import LfzkV2.Current.ZeroKnowledge.FrontendAdapterCorrectness
import LfzkV2.Current.ProtocolWrites

/-! A body-free prover-side reader for the current chained oracle keys.
Only the already bound public prefix, actual prior answers, and pending
public writes occur in this state. Constructing a round does not receive a
complete proof, a witness, or a callback which could inspect future fields.

The last answer is retained solely to extend the final combine squeeze for
input-only assertions. Every other callback makes exactly one boundary query
and feeds back that same query's actual link. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteTranscript
open SumcheckV2
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}

abbrev Fresh := ProtocolWrites.Fresh g fields Advice
abbrev Block := Base × Fresh (g := g) (fields := fields) (Advice := Advice)
abbrev Point := Replay.Point g fields Advice Authentication Key
  (Block (g := g) (fields := fields) (Advice := Advice) (Base := Base))

structure State (g : Geometry) (fields : Fields) (Advice Key Base C : Type) where
  rank : Fin (g.roles.length+1)
  history : History Key (Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest rank.val
  past : Fin rank.val → C
  writes : Fin rank.val → Fresh (g := g) (fields := fields) (Advice := Advice)
  pending : Fresh (g := g) (fields := fields) (Advice := Advice)
  lastAnswer : C

def initial (context : Key) (fallback : C) : State g fields Advice Key Base C :=
  ⟨⟨0,by omega⟩,context,Fin.elim0,Fin.elim0,{},fallback⟩

def currentBlock
    (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
      (Fin i.val → C) → Base)
    (state : State g fields Advice Key Base C) (hrank : state.rank.val < g.roles.length) :
    Block (g := g) (fields := fields) (Advice := Advice) (Base := Base) :=
  (bindOnly ⟨state.rank.val,hrank⟩ (Fin.snoc state.writes state.pending) state.past,state.pending)

def query
    (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
      (Fin i.val → C) → Base)
    (state : State g fields Advice Key Base C) (hrank : state.rank.val < g.roles.length) :
    Point (g := g) (fields := fields) (Advice := Advice) (Authentication := Authentication)
      (Key := Key) (Base := Base) :=
  .round ⟨state.rank.val,hrank⟩ state.history (currentBlock bindOnly state hrank)

def advance
    (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
      (Fin i.val → C) → Base)
    (state : State g fields Advice Key Base C) (hrank : state.rank.val < g.roles.length)
    (answer : Digest × C) : State g fields Advice Key Base C where
  rank := ⟨state.rank.val+1,by omega⟩
  history := (state.history,currentBlock bindOnly state hrank,answer.1)
  past := Fin.snoc state.past answer.2
  writes := Fin.snoc state.writes state.pending
  pending := {}
  lastAnswer := answer.2

def step
    (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
      (Fin i.val → C) → Base)
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Authentication := Authentication)
      (Key := Key) (Base := Base) → Digest × C)
    (state : State g fields Advice Key Base C) : C × State g fields Advice Key Base C :=
  if hrank : state.rank.val < g.roles.length then
    let answer := H (query bindOnly state hrank)
    (answer.2,advance bindOnly state hrank answer)
  else (state.lastAnswer,state)

theorem step_query
    (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
      (Fin i.val → C) → Base)
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Authentication := Authentication)
      (Key := Key) (Base := Base) → Digest × C)
    (state : State g fields Advice Key Base C) (hrank : state.rank.val < g.roles.length) :
    step bindOnly H state =
      ((H (query bindOnly state hrank)).2,advance bindOnly state hrank (H (query bindOnly state hrank))) := by
  simp only [step,dif_pos hrank]

theorem advance_feedback
    (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
      (Fin i.val → C) → Base)
    (state : State g fields Advice Key Base C) (hrank : state.rank.val < g.roles.length)
    (answer : Digest × C) (initialLink : Digest) :
    Input.lastLink initialLink (advance bindOnly state hrank answer).rank.val
      (advance bindOnly state hrank answer).history = answer.1 := rfl

def bind (state : State g fields Advice Key Base C)
    (writes : Fresh (g := g) (fields := fields) (Advice := Advice) →
      Fresh (g := g) (fields := fields) (Advice := Advice)) : State g fields Advice Key Base C :=
  { state with pending := writes state.pending }

def frontend (side : Side) (state : State g fields Advice Key Base C)
    (message : Layered.Replay.Message (fields side)) : State g fields Advice Key Base C :=
  bind state fun writes => { writes with frontend := Function.update writes.frontend side message }

def mapMessage {E F : Type} (field : E → F) : Layered.Replay.Message E → Layered.Replay.Message F
  | .empty => .empty
  | .round polynomial => .round ⟨field polynomial.c0,field polynomial.c1⟩
  | .cross cross => .cross (field cross)
  | .claims a b => .claims (field a) (field b)

theorem mapMessage_inverse {E F : Type} (field : E ≃ F) (message : Layered.Replay.Message F) :
    mapMessage field (mapMessage field.symm message) = message := by
  cases message with
  | empty => rfl
  | round polynomial => cases polynomial; simp [mapMessage]
  | cross => simp [mapMessage]
  | claims => simp [mapMessage]

def reader {F : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
      (Fin i.val → C) → Base)
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Authentication := Authentication)
      (Key := Key) (Base := Base) → Digest × C) :
    CircuitReader F (State g fields Advice Key Base C) where
  round state polynomial :=
    let answer := step bindOnly H (frontend side state (mapMessage field.symm (.round polynomial)))
    (decode answer.1 0,answer.2)
  terminal state cross :=
    let answer := step bindOnly H (frontend side state (mapMessage field.symm (.cross cross)))
    (nonzero answer.1,answer.2)
  combine state factors :=
    let answer := step bindOnly H (frontend side state (mapMessage field.symm (.claims factors.1 factors.2)))
    (decode answer.1 0,answer.2)
  assertions state count :=
    let answer := step bindOnly H state
    (fun i : Fin count => decode answer.1 i.val,answer.2)
  inputAssertions state count := (fun i : Fin count => decode state.lastAnswer (1+i.val),state)

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteTranscript
