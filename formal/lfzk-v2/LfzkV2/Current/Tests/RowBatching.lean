import LfzkV2.Current.PureComposition

/-! Row batching of a pure-foreign participant, its handoff to the adapter
and its composition with the binary frontend. -/
noncomputable section
namespace LfzkV2.Current.Tests.RowBatching
open LfzkV2.Current.RowBatching
open scoped Classical

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Two false rows can cancel in one combination: the batching event is real
-- and must be charged, rather than assumed away.
def cancelling : Fin 2 → LfzkV2.LinearRow Unit (ZMod 5)
  | 0 => ⟨1, []⟩
  | 1 => ⟨4, []⟩
example : Bad cancelling (fun _ => 0) (fun _ => 1) := by
  refine ⟨fun h => absurd (h 0) ?_, ?_⟩
  · simp [cancelling, SumcheckV2.PadExpression.eval]
  · rw [batch_residual]
    simp [cancelling, SumcheckV2.PadExpression.eval, Fin.sum_univ_two]
    decide
example : ¬ Bad cancelling (fun _ => 0) ![1, 2] := by
  rintro ⟨-, h⟩
  rw [batch_residual] at h
  simp [cancelling, SumcheckV2.PadExpression.eval, Fin.sum_univ_two] at h
  revert h
  decide

-- The batched coefficients and target follow the runtime's formula: one
-- layer row `2*v + 1` and the input row `3 - v`, weighted by `rho = (1, 2)`.
def layer : Fin 1 → LfzkV2.LinearRow Unit (ZMod 5) := fun _ => ⟨1, [((), 2)]⟩
def input : LfzkV2.LinearRow Unit (ZMod 5) := ⟨3, [((), -1)]⟩
example : (batch (ofLayers layer input) ![1, 2]).weights () = 0 := by
  rw [batch_ofLayers_weights]
  simp [layer, input, Prime.coefficients]
example : (batch (ofLayers layer input) ![1, 2]).target = 3 := by
  rw [batch_ofLayers_target]
  simp [layer, input]
  decide

-- A foreign value is the residue of its bits; the bits need not encode a
-- canonical integer. Three set bits of one value read `7 = 2 (mod 5)`.
def oneValue : PureHandoff.Groups Unit 3 := ⟨fun _ => (), fun i => i.val⟩
example : oneValue.value (p := 5) (fun _ => true) () = 2 := by
  simp [PureHandoff.Groups.value, oneValue, Fin.sum_univ_three]
  decide
example : oneValue.weights (p := 5) (fun _ => 3) 2 = 2 := by
  simp [PureHandoff.Groups.weights, oneValue]
  decide

-- For the P-256-sized prime field the batching error is `1/p`.
example {p n : ℕ} [Fact p.Prime] {Value : Type} [Fintype Value]
    (rows : Fin n → LfzkV2.LinearRow Value (ZMod p)) (values : Value → ZMod p) :
    ((Finset.univ.filter (Bad rows values)).card : ℚ) / Fintype.card (Fin n → ZMod p) ≤
      1 / p := by
  simpa [ZMod.card] using bad_probability_le rows values

#print axioms RowBatching.batch_residual
#print axioms RowBatching.batch_ofLayers_weights
#print axioms RowBatching.batch_ofLayers_target
#print axioms RowBatching.bad_card_mul_le
#print axioms RowBatching.bad_probability_le
#print axioms PureHandoff.Groups.residual_eq
#print axioms PureHandoff.pure_handoff
#print axioms PureHandoff.conversion_card_le
#print axioms PureHandoff.bad_card_mul_le
#print axioms PureHandoff.bad_probability_le
#print axioms PureHandoff.Data.bad_card_mul_le
#print axioms PureComposition.rows_reduction

end LfzkV2.Current.Tests.RowBatching
