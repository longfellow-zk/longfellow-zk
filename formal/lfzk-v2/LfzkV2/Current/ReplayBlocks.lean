import LfzkV2.Current.ReplayPrefix

/-! Recover the actual block written at a replay boundary.  Parent recovery
alone does not establish the connection between a decoded prover message and
the block hashed by the verifier.  These lemmas give that connection directly
from `Encoding.advance`, including the strict-prefix answer tape. -/
namespace LfzkV2.Current

namespace Input
variable {roles : List Role} {Context Block Link Body : Type}

def block : Input roles Context Block Link Body → Option Block
  | .round _ _ block => some block
  | .finalSeal .. => none

end Input

namespace Replay
variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C : Type}

def State.BlockBound (state : State g F Advice Authentication Context Block C)
    (e : Encoding g F Advice Authentication Context Block C)
    (proof : Output g F Advice Authentication) : Prop :=
  ∀ i history block, (h : state.point = .round i history block) →
    ∃ answers : Fin i.val → C, block = e.block proof i answers ∧
      ∀ j, answers j = state.answers ⟨j.val, by
        have hr := congrArg Input.rank h
        change state.point.rank = i.val at hr
        rw [hr]
        exact j.isLt⟩

namespace Encoding
variable (e : Encoding g F Advice Authentication Context Block C)

theorem stateAt_block (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) : (e.stateAt proof n hn history answers).BlockBound e proof := by
  by_cases h : n < g.roles.length
  · have hs : e.stateAt proof n hn history answers =
        ⟨.round ⟨n,h⟩ history (e.block proof ⟨n,h⟩ answers), answers⟩ := dif_pos h
    rw [hs]
    intro i earlier block heq
    cases heq
    exact ⟨answers, rfl, fun _ => rfl⟩
  · have he : n = g.roles.length := by omega
    subst n
    intro i earlier block heq
    simp only [stateAt, dif_neg h] at heq
    cases heq

theorem advance_block (proof : Output g F Advice Authentication)
    (state : State g F Advice Authentication Context Block C) (answer : Digest × C)
    (hs : state.BlockBound e proof) : (e.advance proof state answer).BlockBound e proof := by
  rcases state with ⟨point, answers⟩
  cases point with
  | round i history block => exact e.stateAt_block proof _ _ _ _
  | finalSeal history body => exact hs

theorem replay_block (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C) (n : ℕ) :
    ((e.chain initialLink).replay proof H n).BlockBound e proof := by
  induction n with
  | zero => exact e.stateAt_block proof 0 (Nat.zero_le _) _ _
  | succ n ih =>
      by_cases hn : n < g.roles.length
      · simpa only [TranscriptV2.Chain.replay, TranscriptV2.Chain.point, dif_pos hn, chain] using
          e.advance_block proof ((e.chain initialLink).replay proof H n)
            (H ((e.chain initialLink).point proof H n)) ih
      · simpa only [TranscriptV2.Chain.replay, dif_neg hn] using ih

/-- The current block contains exactly the encoder's writes using strict
prior answers.  This holds for every proof, before any acceptance assumption. -/
theorem point_block (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C)
    (i : Fin g.roles.length) :
    ((e.chain initialLink).point proof H i.val).block =
      some (e.block proof i (fun j => (H ((e.chain initialLink).point proof H j.val)).2)) := by
  have hb := e.replay_block initialLink proof H i.val
  have hc := e.replay_coherent initialLink proof H i.val
  have hr := (e.chain initialLink).point_rank proof H (show i.val ≤ g.roles.length by omega)
  change Input.rank _ = i.val at hr
  cases heq : (e.chain initialLink).point proof H i.val with
  | finalSeal history body =>
      rw [heq] at hr
      have hi := i.isLt
      change g.roles.length = i.val at hr
      omega
  | round j history block =>
      have hj : j = i := Fin.ext (by simpa only [heq, Input.rank] using hr)
      subst j
      obtain ⟨answers, hblock, ha⟩ := hb i history block heq
      have hanswers : answers = fun j => (H ((e.chain initialLink).point proof H j.val)).2 := by
        funext j
        rw [ha j]
        have hs := congrFun hc ⟨j.val, by
          change j.val < ((e.chain initialLink).point proof H i.val).rank
          rw [hr]
          exact j.isLt⟩
        change _ = (H (((e.chain initialLink).point proof H i.val).priorPoints _)).2 at hs
        rw [hs]
        exact congrArg (fun point => (H point).2)
          (e.point_priorPoints initialLink proof H i.val (by omega) j)
      rw [hanswers] at hblock
      simpa only [heq, Input.block] using congrArg some hblock

end Encoding
end Replay
end LfzkV2.Current
