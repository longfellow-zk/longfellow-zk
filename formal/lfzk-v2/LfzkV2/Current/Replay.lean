import LfzkV2.Current.ReplayTranscript
import TranscriptV2.Replay

/-! Verifier execution pairs transcript state with a challenge cache used
for arithmetic. The general encoding interface can inspect earlier answers;
canonical encoders prove that their written packets do not. `replay_transcript`
then projects execution to the separate digest-only transcript replay. -/
namespace LfzkV2.Current.Replay

variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C : Type}

/-- The complete proof owns its messages and terminal body. The current
canonical builders ignore the general interface's earlier-answer argument;
challenge-derived affine rows and adapter equations remain verifier-local. -/
structure Encoding (g : Geometry) (F : Fields)
    (Advice Authentication Context Block C : Type) where
  context : Output g F Advice Authentication → Context
  block : Output g F Advice Authentication →
    (i : Fin g.roles.length) → (Fin i.val → C) → Block

abbrev VerifierState (C : Type) (rounds : ℕ) := Fin rounds → C

/-- The generic execution adapter pairs transcript and verifier states.
`Transcript` supplies the separate digest-only transition system. -/
structure State (g : Geometry) (F : Fields) (Advice Authentication Context Block C : Type) where
  point : TranscriptState g F Advice Authentication Context Block
  answers : VerifierState C point.rank

def State.Coherent (state : State g F Advice Authentication Context Block C)
    (H : Point g F Advice Authentication Context Block → Digest × C) : Prop :=
  state.answers = state.point.priorAnswers H

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

/-- Freeze the written packets, discarding the verifier's cache. The
independence law below proves that the chosen default does not affect them. -/
def transcript (proof : Output g F Advice Authentication) (fallback : C) :
    Transcript g F Advice Authentication Context Block where
  context := e.context proof
  block i := e.block proof i (fun _ => fallback)
  body := proof.body

variable (proof : Output g F Advice Authentication) (fallback : C)
variable (independent : ∀ i first second, e.block proof i first = e.block proof i second)

include independent in
private theorem stateAt_transcript (n : ℕ) (hn : n ≤ g.roles.length)
    (history : History Context Block Digest n) (answers : Fin n → C) :
    (e.stateAt proof n hn history answers).point =
      TranscriptState.atRound proof.body n hn history
        (fun h => (e.transcript proof fallback).block ⟨n,h⟩) := by
  by_cases h : n < g.roles.length
  · simp only [stateAt,TranscriptState.atRound,dif_pos h,transcript]
    rw [independent ⟨n,h⟩ answers (fun _ => fallback)]
  · have he : n = g.roles.length := by omega
    subst n
    simp [stateAt,TranscriptState.atRound]

include independent in
/-- Transcript evolution is independent of the execution's challenge
cache; only the digest component of the new answer crosses the boundary. -/
theorem advance_transcript (state : State g F Advice Authentication Context Block C)
    (answer : Digest × C) :
    (e.advance proof state answer).point =
      (e.transcript proof fallback).advance state.point answer.1 := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round i history block => exact e.stateAt_transcript proof fallback independent _ _ _ _
  | finalSeal history body => rfl

include independent in
/-- The existing verifier execution projects exactly to the separate
digest-only transcript. Arithmetic caches need not be compared. -/
theorem replay_transcript (initialLink : Digest)
    (H : Point g F Advice Authentication Context Block → Digest × C) (n : ℕ) :
    (e.chain initialLink).point proof H n =
      (e.transcript proof fallback).replay (fun point => (H point).1) n := by
  induction n with
  | zero => exact e.stateAt_transcript proof fallback independent _ _ _ _
  | succ n ih =>
      by_cases inside : n < g.roles.length
      · simp only [TranscriptV2.Chain.point,TranscriptV2.Chain.replay,dif_pos inside]
        change (e.advance proof ((e.chain initialLink).replay proof H n)
          (H ((e.chain initialLink).point proof H n))).point = _
        rw [e.advance_transcript proof fallback independent]
        change (e.transcript proof fallback).advance
          ((e.chain initialLink).point proof H n) (H ((e.chain initialLink).point proof H n)).1 = _
        rw [ih]
        exact (if_pos inside).symm
      · simpa only [TranscriptV2.Chain.point,TranscriptV2.Chain.replay,dif_neg inside,
          Transcript.replay,if_neg inside] using ih

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
    (answers : Fin n → C) : (e.stateAt proof n hn history answers).point.BodyBound proof.body := by
  by_cases h : n < g.roles.length
  · simp [stateAt, h, TranscriptState.BodyBound]
  · have he : n = g.roles.length := by omega
    subst n
    intro other body heq
    exact (Input.finalSeal_body_bound (by simpa [stateAt] using heq)).symm

theorem advance_body (proof : Output g F Advice Authentication)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C)
    (hs : state.point.BodyBound proof.body) : (e.advance proof state answer).point.BodyBound proof.body := by
  rcases state with ⟨point,answers⟩
  cases point with
  | round j history block => exact e.stateAt_body proof _ _ _ _
  | finalSeal history body => exact hs

theorem replay_body (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C) (n : ℕ) :
    TranscriptState.BodyBound ((e.chain initialLink).point proof H n) proof.body := by
  induction n with
  | zero => exact e.stateAt_body proof 0 (Nat.zero_le _) _ _
  | succ n ih =>
      by_cases hn : n < g.roles.length
      · simpa only [TranscriptV2.Chain.replay, TranscriptV2.Chain.point, dif_pos hn, chain] using
          e.advance_body proof ((e.chain initialLink).replay proof H n)
            (H ((e.chain initialLink).point proof H n)) ih
      · simpa only [TranscriptV2.Chain.point, TranscriptV2.Chain.replay, dif_neg hn] using ih

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
