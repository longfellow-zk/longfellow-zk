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
  state.point.block = if h : state.point.rank < g.roles.length then
    some (e.block proof ⟨state.point.rank,h⟩ state.answers) else none

namespace Encoding
variable (e : Encoding g F Advice Authentication Context Block C)

theorem stateAt_block (proof : Output g F Advice Authentication)
    (n : ℕ) (hn : n ≤ g.roles.length) (history : History Context Block Digest n)
    (answers : Fin n → C) : (e.stateAt proof n hn history answers).BlockBound e proof := by
  by_cases h : n < g.roles.length
  · simp only [stateAt,dif_pos h]
    simp only [State.BlockBound,Input.block,Input.rank,dif_pos h]
  · have he : n = g.roles.length := by omega
    subst n
    simp [stateAt,State.BlockBound,Input.block,Input.rank]

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
  have hr := (e.chain initialLink).point_rank proof H (show i.val ≤ g.roles.length by omega)
  change Input.rank _ = i.val at hr
  have inside : ((e.chain initialLink).point proof H i.val).rank < g.roles.length := by
    rw [hr]
    exact i.isLt
  have answers := funext (e.replay_answer initialLink proof H i.val (Nat.le_of_lt i.isLt))
  change ((e.chain initialLink).point proof H i.val).block =
    (if h : ((e.chain initialLink).point proof H i.val).rank < g.roles.length then
      some (e.block proof ⟨_,h⟩ ((e.chain initialLink).replay proof H i.val).answers)
    else none) at hb
  rw [dif_pos inside,answers] at hb
  let packet := fun j : Fin g.roles.length =>
    e.block proof j (fun k => (H ((e.chain initialLink).point proof H k.val)).2)
  change ((e.chain initialLink).point proof H i.val).block = some (packet ⟨_,inside⟩) at hb
  have index : (⟨_,inside⟩ : Fin g.roles.length) = i := Fin.ext hr
  rw [index] at hb
  exact hb

end Encoding
end Replay
end LfzkV2.Current
