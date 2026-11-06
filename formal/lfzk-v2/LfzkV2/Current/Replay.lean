import LfzkV2.Current.Prefix
import TranscriptV2.Replay

/-! Replay of the current round schedule with actual link feedback. The state
retains earlier challenge answers for deriving later statements, but only the
link is absorbed into the logical query history. Boundary encodings may read
earlier answers, never their own answer. Identifying these encodings with the
canonical Rust messages remains an implementation correspondence obligation. -/
namespace LfzkV2.Current.Replay

variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C : Type}

abbrev Output (g : Geometry) (F : Fields) (Advice Authentication : Type) :=
  Proof g F Advice Authentication

abbrev Point (g : Geometry) (F : Fields) (Advice Authentication Context Block : Type) :=
  Input g.roles Context Block Digest (Body g F Advice Authentication)

/-- The complete proof supplies messages; prior answers supply derived public
data such as the adapter equation and the compiled affine rows. The
complete body and its seal are deliberately not configurable here. -/
structure Encoding (g : Geometry) (F : Fields)
    (Advice Authentication Context Block C : Type) where
  context : Output g F Advice Authentication → Context
  block : Output g F Advice Authentication →
    (i : Fin g.roles.length) → (Fin i.val → C) → Block

structure State (g : Geometry) (F : Fields) (Advice Authentication Context Block C : Type) where
  point : Point g F Advice Authentication Context Block
  answers : Fin point.rank → C

def State.Coherent (state : State g F Advice Authentication Context Block C)
    (H : Point g F Advice Authentication Context Block → Digest × C) : Prop :=
  state.answers = state.point.priorAnswers H

def State.BodyBound (state : State g F Advice Authentication Context Block C)
    (proof : Output g F Advice Authentication) : Prop :=
  ∀ history body, state.point = .finalSeal history body → body = proof.body

namespace Encoding
variable (e : Encoding g F Advice Authentication Context Block C)

def stateAt (proof : Output g F Advice Authentication) (n : ℕ) (hn : n ≤ g.roles.length)
    (history : History Context Block Digest n) (answers : Fin n → C) :
    State g F Advice Authentication Context Block C :=
  if h : n < g.roles.length then
    ⟨.round ⟨n,h⟩ history (e.block proof ⟨n,h⟩ answers), answers⟩
  else by
    have he : n = g.roles.length := by omega
    subst n
    exact ⟨.finalSeal history proof.body, answers⟩

@[simp] theorem stateAt_rank (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) : (e.stateAt proof n hn history answers).point.rank = n := by
  by_cases h : n < g.roles.length
  · simp only [stateAt, dif_pos h, Input.rank]
  · have he : n = g.roles.length := by omega
    subst n
    simp [stateAt, Input.rank]

def initial (proof : Output g F Advice Authentication) :
    State g F Advice Authentication Context Block C :=
  e.stateAt proof 0 (Nat.zero_le _) (e.context proof) Fin.elim0

theorem stateAt_parent (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) :
    Input.parent (e.stateAt proof n hn history answers).point = Input.previous n hn history := by
  by_cases h : n < g.roles.length
  · simp only [stateAt, dif_pos h, Input.parent]
  · have he : n = g.roles.length := by omega
    subst n
    simp [stateAt, Input.parent]

theorem stateAt_link (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) (initialLink : Digest) :
    Input.claimed initialLink (e.stateAt proof n hn history answers).point =
      Input.lastLink initialLink n history := by
  by_cases h : n < g.roles.length
  · simp only [stateAt, dif_pos h, Input.claimed]
  · have he : n = g.roles.length := by omega
    subst n
    simp [stateAt, Input.claimed]

theorem stateAt_context (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) :
    (e.stateAt proof n hn history answers).point.context = Input.historyContext n history := by
  by_cases h : n < g.roles.length
  · simp only [stateAt, dif_pos h, Input.context]
  · have he : n = g.roles.length := by omega
    subst n
    simp [stateAt, Input.context]

def advance (proof : Output g F Advice Authentication)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C) :
    State g F Advice Authentication Context Block C :=
  match state with
  | ⟨.round i history block, answers⟩ =>
      e.stateAt proof (i.val+1) (by omega) (history, block, answer.1) (Fin.snoc answers answer.2)
  | ⟨.finalSeal history body, answers⟩ => ⟨.finalSeal history body, answers⟩

theorem advance_rank (proof : Output g F Advice Authentication) (i : Fin g.roles.length)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C)
    (h : state.point.rank = i.val) :
    (e.advance proof state answer).point.rank = i.val+1 := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round j history block =>
      change (e.stateAt proof (j.val+1) _ _ _).point.rank = i.val+1
      rw [stateAt_rank]
      exact congrArg (·+1) h
  | finalSeal history body =>
      have hi := i.isLt
      simp only [Input.rank] at h
      omega

theorem advance_parent (proof : Output g F Advice Authentication) (i : Fin g.roles.length)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C)
    (h : state.point.rank = i.val) :
    Input.parent (e.advance proof state answer).point = some state.point := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round j history block =>
      change Input.parent (e.stateAt proof (j.val+1) _ _ _).point = _
      rw [stateAt_parent]
      rfl
  | finalSeal history body =>
      have hi := i.isLt
      simp only [Input.rank] at h
      omega

theorem advance_link (proof : Output g F Advice Authentication) (i : Fin g.roles.length)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C)
    (h : state.point.rank = i.val) (initialLink : Digest) :
    Input.claimed initialLink (e.advance proof state answer).point = answer.1 := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round j history block =>
      change Input.claimed initialLink (e.stateAt proof (j.val+1) _ _ _).point = _
      rw [stateAt_link]
      rfl
  | finalSeal history body =>
      have hi := i.isLt
      simp only [Input.rank] at h
      omega

def chain (initialLink : Digest) : TranscriptV2.Chain
    (Point g F Advice Authentication Context Block) Digest C
    (Output g F Advice Authentication) g.roles.length where
  parent := Input.parent
  claimed := Input.claimed initialLink
  State := State g F Advice Authentication Context Block C
  rank := Input.rank
  initial := e.initial
  input := State.point
  advance proof _ state answer := e.advance proof state answer
  initial_rank proof := e.stateAt_rank proof 0 (Nat.zero_le _) (e.context proof) Fin.elim0
  advance_rank := e.advance_rank
  advance_parent := e.advance_parent
  advance_link proof i state answer h := e.advance_link proof i state answer h initialLink
  finalSeal := Proof.finalSeal

theorem stateAt_coherent (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) (H : Point g F Advice Authentication Context Block → Digest × C)
    (ha : answers = fun i => (H (Input.historyPoints n hn history i)).2) :
    (e.stateAt proof n hn history answers).Coherent H := by
  by_cases h : n < g.roles.length
  · have hs : e.stateAt proof n hn history answers =
        ⟨.round ⟨n,h⟩ history (e.block proof ⟨n,h⟩ answers), answers⟩ := dif_pos h
    rw [hs]
    exact ha
  · have he : n = g.roles.length := by omega
    subst n
    have hs : e.stateAt proof g.roles.length hn history answers =
        ⟨.finalSeal history proof.body, answers⟩ := by simp [stateAt]
    rw [hs]
    exact ha

theorem advance_coherent (proof : Output g F Advice Authentication)
    (state : State g F Advice Authentication Context Block C)
    (H : Point g F Advice Authentication Context Block → Digest × C)
    (hs : state.Coherent H) : (e.advance proof state (H state.point)).Coherent H := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round j history block =>
      apply e.stateAt_coherent
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp only [Fin.snoc_last, Input.historyPoints]
      · simp only [Fin.snoc_castSucc, Input.historyPoints]
        exact congrFun hs k
  | finalSeal history body => exact hs

theorem replay_coherent (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C) (n : ℕ) :
    ((e.chain initialLink).replay proof H n).Coherent H := by
  induction n with
  | zero =>
      apply e.stateAt_coherent
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      by_cases hn : n < g.roles.length
      · simpa only [TranscriptV2.Chain.replay, dif_pos hn, chain] using
          e.advance_coherent proof ((e.chain initialLink).replay proof H n) H ih
      · simpa only [TranscriptV2.Chain.replay, dif_neg hn] using ih

theorem advance_context (proof : Output g F Advice Authentication)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C) :
    (e.advance proof state answer).point.context = state.point.context := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round j history block => exact e.stateAt_context proof _ _ _ _
  | finalSeal history body => rfl

theorem point_context (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C) (n : ℕ) :
    ((e.chain initialLink).point proof H n).context = e.context proof := by
  induction n with
  | zero => exact e.stateAt_context proof 0 (Nat.zero_le _) _ _
  | succ n ih =>
      by_cases hn : n < g.roles.length
      · simpa only [TranscriptV2.Chain.point, TranscriptV2.Chain.replay, dif_pos hn, chain] using
          (e.advance_context proof ((e.chain initialLink).replay proof H n)
            (H ((e.chain initialLink).point proof H n))).trans ih
      · simpa only [TranscriptV2.Chain.point, TranscriptV2.Chain.replay, dif_neg hn] using ih

theorem stateAt_body (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) : (e.stateAt proof n hn history answers).BodyBound proof := by
  by_cases h : n < g.roles.length
  · simp [stateAt, h, State.BodyBound]
  · have he : n = g.roles.length := by omega
    subst n
    intro other body heq
    exact (Input.finalSeal_body_bound (by simpa [stateAt] using heq)).symm

theorem advance_body (proof : Output g F Advice Authentication)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C)
    (hs : state.BodyBound proof) : (e.advance proof state answer).BodyBound proof := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round j history block => exact e.stateAt_body proof _ _ _ _
  | finalSeal history body => exact hs

theorem replay_body (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C) (n : ℕ) :
    ((e.chain initialLink).replay proof H n).BodyBound proof := by
  induction n with
  | zero => exact e.stateAt_body proof 0 (Nat.zero_le _) _ _
  | succ n ih =>
      by_cases hn : n < g.roles.length
      · simpa only [TranscriptV2.Chain.replay, TranscriptV2.Chain.point, dif_pos hn, chain] using
          e.advance_body proof ((e.chain initialLink).replay proof H n)
            (H ((e.chain initialLink).point proof H n)) ih
      · simpa only [TranscriptV2.Chain.replay, dif_neg hn] using ih

/-- Final replay necessarily reaches the separately framed complete body.
The earlier queries and the final seal are all covered by this same chain. -/
theorem finalSealPoint_body (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C) :
    ∃ history, (e.chain initialLink).finalSealPoint proof H = .finalSeal history proof.body := by
  have hr := (e.chain initialLink).point_rank proof H (Nat.le_refl g.roles.length)
  have hb := e.replay_body initialLink proof H g.roles.length
  change ((e.chain initialLink).finalSealPoint proof H).rank = g.roles.length at hr
  change ∀ history body, (e.chain initialLink).finalSealPoint proof H = .finalSeal history body →
    body = proof.body at hb
  cases he : (e.chain initialLink).finalSealPoint proof H with
  | round i history block =>
      rw [he] at hr
      have hi := i.isLt
      simp only [Input.rank] at hr
      omega
  | finalSeal history body =>
      have hbody := hb history body he
      subst body
      exact ⟨history,rfl⟩

end Encoding
end LfzkV2.Current.Replay
