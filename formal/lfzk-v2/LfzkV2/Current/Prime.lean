import LfzkV2.Linear.TerminalSampling
import LfzkV2.Layered.Soundness
import LigeroFamily.Protocol.Finite

/-! The current prime frontend has mixed storage (`zk/src/split.rs`): it
commits its native private inputs, the hiding scalar R and its pads, and every
pad is native. The layer rows read only pads, so they enter the prime
statement unbatched. Only the final input equation reads the shared bits; it
is split with a nonzero eta and the masked message `mu = eta*<w_F, v_F> + R`.
The binary participant contains its own copy of R: equality is a consequence
of the rescaling check, never an extraction premise. -/
namespace LfzkV2.Current.Prime
open Finset SumcheckV2
open scoped Classical

variable {F Slot Shared Other : Type} [Field F]

/-- Algebraic form of `split.rs::SplitClaim` for mixed storage. `layers` are
the layer rows on native cells. The input equation is `<w, v> = target` with
`w` split into the shared (foreign) and the other (native) values. `Other`
contains the remaining prime inputs and all prime pads; neither vector
includes the hiding scalar. -/
structure Claim (Shared Other F : Type) where
  layers : List (LinearRow Other F)
  sharedWeights : Shared → F
  otherWeights : Other → F
  target : F

/-- A layer row on the participant's cells, which also contain R. -/
def layerRow (row : LinearRow Other F) : LinearRow (Other ⊕ Unit) F :=
  ⟨row.constant, mapTerms row.terms Sum.inl⟩

theorem layerRow_eval (row : LinearRow Other F) (other : Other → F) (mask : F) :
    (layerRow row).eval (Sum.elim other (fun _ => mask)) = row.eval other := by
  simp [layerRow, PadExpression.eval, mapTerms, Function.comp_def]

variable [Fintype Shared] [Fintype Other]

def Claim.residual (c : Claim Shared Other F) (shared : Shared → F) (other : Other → F) : F :=
  (∑ i, c.sharedWeights i * shared i) + (∑ i, c.otherWeights i * other i) - c.target

/-- Exactly the native row `eta*<w_N, v_N> - R + mu - eta*t` of `split_statement`. -/
noncomputable def Claim.row (c : Claim Shared Other F) (eta mu : F) : LinearRow (Other ⊕ Unit) F where
  constant := mu - eta * c.target
  terms := (univ.toList.map fun i => (Sum.inl i, eta * c.otherWeights i)) ++ [(Sum.inr (), -1)]

omit [Fintype Shared] in
theorem Claim.row_eval (c : Claim Shared Other F) (eta mu mask : F) (other : Other → F) :
    (c.row eta mu).eval (Sum.elim other (fun _ => mask)) =
      eta * (∑ i, c.otherWeights i * other i) - mask + mu - eta * c.target := by
  simp [Claim.row, PadExpression.eval, mul_assoc, mul_sum]
  ring

/-- The complete prime statement of `split_statement`: rows `0..L-1` are the
unbatched layer rows, row `L` is the native part of the input equation. -/
noncomputable def Claim.rows (c : Claim Shared Other F) (eta mu : F) : List (LinearRow (Other ⊕ Unit) F) :=
  c.layers.map layerRow ++ [c.row eta mu]

omit [Fintype Shared] in
theorem Claim.rows_length (c : Claim Shared Other F) (eta mu : F) :
    (c.rows eta mu).length = c.layers.length+1 := by
  simp [Claim.rows]

omit [Fintype Shared] in
theorem Claim.rows_hold_iff (c : Claim Shared Other F) (eta mu mask : F) (other : Other → F) :
    RowsHold (c.rows eta mu) (Sum.elim other (fun _ => mask)) ↔
      RowsHold c.layers other ∧ (c.row eta mu).eval (Sum.elim other (fun _ => mask)) = 0 := by
  simp only [RowsHold, Claim.rows, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_singleton, layerRow_eval]

def RescalingBad (residual difference eta : F) : Prop :=
  residual ≠ 0 ∧ eta * residual + difference = 0

theorem rescaling_bad_card [Fintype F] [DecidableEq F] (residual difference : F) :
    (univ.filter fun eta : Linear.TerminalSampling.Nonzero F =>
      RescalingBad residual difference eta.val).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨hr, ha⟩ := (mem_filter.mp ha).2
  have hb := (mem_filter.mp hb).2.2
  exact Subtype.ext (mul_right_cancel₀ hr (add_right_cancel (ha.trans hb.symm)))

/-- Combining the binary opening with the prime row leaves one affine
equation in eta, even if the two extracted masks differ. -/
theorem Claim.handoff (c : Claim Shared Other F) (shared : Shared → F) (other : Other → F)
    (eta mu binaryMask primeMask : F)
    (hadapter : mu = eta * (∑ i, c.sharedWeights i * shared i) + binaryMask)
    (hrow : (c.row eta mu).eval (Sum.elim other (fun _ => primeMask)) = 0) :
    eta * c.residual shared other + (binaryMask - primeMask) = 0 := by
  rw [c.row_eval, hadapter] at hrow
  dsimp [Claim.residual]
  linear_combination hrow

theorem Claim.true_or_rescaling_bad (c : Claim Shared Other F)
    (shared : Shared → F) (other : Other → F) (eta mu binaryMask primeMask : F)
    (hadapter : mu = eta * (∑ i, c.sharedWeights i * shared i) + binaryMask)
    (hrow : (c.row eta mu).eval (Sum.elim other (fun _ => primeMask)) = 0) :
    (c.residual shared other = 0 ∧ binaryMask = primeMask) ∨
      RescalingBad (c.residual shared other) (binaryMask - primeMask) eta := by
  have h := c.handoff shared other eta mu binaryMask primeMask hadapter hrow
  by_cases hz : c.residual shared other = 0
  · exact Or.inl ⟨hz, by simpa [hz, sub_eq_zero] using h⟩
  · exact Or.inr ⟨hz, h⟩

end LfzkV2.Current.Prime
