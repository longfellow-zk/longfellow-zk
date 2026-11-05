import LfzkV2.Layered.Runtime.CompiledSide
import LfzkV2.Joint.Backend

/-! Reuse the actual field-specific compiler and its proved transfer. A
frontend result contains its packing scalar, but no backend response. This
is the boundary passed to the next field before joint backend challenges. -/

namespace LfzkV2.Layered.Joint

open RecursivePolygero Bcs.TotalOracle

namespace Side

variable {F C Context : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input : ℕ} {circuit : Layered.Circuit F out input} {I : Instance F}
variable (S : Layered.Runtime.CompiledSide F C Context circuit I)

abbrev Frontend := S.Parent × F

def steps : ℕ := Layered.Replay.slots circuit + Layered.Runtime.Replay.packingSlots S.packed

theorem steps_add_two : steps S + 2 = S.slots := rfl

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem native_ancestor_slot {Key : Type}
    (p : Layered.Replay.Point Key F circuit) (j : ℕ)
    (hj : j < (Layered.Replay.points circuit).slot p) :
    (Layered.Replay.points circuit).slot ((Layered.Replay.points circuit).anc p j) = j := by
  rcases p with ⟨key, p⟩
  cases p with
  | none => exact (Nat.not_lt_zero j hj).elim
  | some p =>
      change j < p.1.val at hj
      simp only [Layered.Replay.points, Transcript.ancestor, dif_pos hj]

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem native_slot {Key : Type} (key : Key) (payload : Layered.Replay.Payload circuit)
    (j : ℕ) (hj : j < Layered.Replay.slots circuit) :
    (Layered.Replay.points circuit).slot (Layered.Replay.hashInput circuit key payload j) = j := by
  rw [Layered.Replay.hashInput, dif_pos hj]
  rfl

/-- The old per-field schedule remains useful as a local proof device. Its
ancestor slots are replayed at their new positions in the joint schedule. -/
theorem ancestor_slot (p : S.Domain) (j : ℕ) (hj : j < S.points.slot p) :
    S.points.slot (S.points.anc p j) = j := by
  rcases p with p | p | p | p
  · exact native_ancestor_slot p j hj
  · exact native_slot _ _ j hj
  · simp only [Layered.Runtime.CompiledSide.points, Layered.Runtime.Replay.points] at hj ⊢
    split_ifs with h
    · exact native_slot _ _ j h
    · cases hp : S.packed <;> simp [hp, Layered.Runtime.Replay.packingSlots,
        Layered.Runtime.Replay.packing] at hj ⊢ <;> omega
  · simp only [Layered.Runtime.CompiledSide.points, Layered.Runtime.Replay.points] at hj ⊢
    split_ifs with hfront hpack
    · exact native_slot _ _ j hfront
    · simp only [Bool.and_eq_true, beq_iff_eq] at hpack
      exact hpack.2.symm
    · cases hp : S.packed <;>
        simp [hp, Layered.Runtime.Replay.packingSlots, Layered.Runtime.Replay.backend] at hj hpack ⊢ <;> omega

theorem backend_at (s : S.Selected) :
    S.hashInput s (steps S) = Layered.Runtime.Replay.backend circuit I s.1 :=
  Layered.Runtime.Replay.backend_at circuit I S.packed Prod.fst (S.frontend ∘ Prod.snd) s

theorem opening_at (s : S.Selected) :
    S.hashInput s (steps S + 1) = Layered.Runtime.Replay.opening circuit I s.1 s.2 :=
  Layered.Runtime.Replay.opening_at circuit I S.packed Prod.fst (S.frontend ∘ Prod.snd) s

/-- No backend response can enter a frontend hash point. -/
theorem frontend_response_irrel (front : Frontend S) (first second : I.layer.Payload)
    (j : ℕ) (hj : j < steps S) :
    S.hashInput (front,first) j = S.hashInput (front,second) j := by
  unfold Layered.Runtime.CompiledSide.hashInput Layered.Runtime.Replay.hashInput
  split_ifs with hfront hpack hback
  · rfl
  · rfl
  · rfl
  · unfold steps at hj
    cases hp : S.packed <;> simp [hp, Layered.Runtime.Replay.packingSlots] at hj hpack
    · omega
    · omega

end Side
end LfzkV2.Layered.Joint
