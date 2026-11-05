import LfzkV2.Joint.Cost
import LfzkV2.Linear.Runtime.Cost

/-! Normalize the joint charges by the common raw-oracle alphabet. Field
samplers retain their own balanced fibers; only the column sampler is shared. -/

namespace LfzkV2.Joint.Cost

open Finset RecursivePolygero Replay

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C] [Nonempty C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Linear.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Linear.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

noncomputable def macCost : ℚ := (S₁.bound : ℚ)*S₂.bound/Fintype.card Fmac

noncomputable def coefficient : ℚ :=
  max (macCost (Fmac := Fmac) S₁ S₂) (max (max S₁.coefficient S₂.coefficient)
    (S₁.potential.queryBudget/Fintype.card C + S₂.potential.queryBudget/Fintype.card C))

noncomputable def constant : ℚ := macCost (Fmac := Fmac) S₁ S₂ + S₁.constant + S₂.constant

theorem macBudget_div_eq :
    ((S₁.bound*S₂.bound*M.fiber : ℕ) : ℚ)/Fintype.card C = macCost (Fmac := Fmac) S₁ S₂ := by
  have hf : (M.fiber : ℚ) ≠ 0 := by
    have hn : M.fiber ≠ 0 := by
      intro hz
      have hb := M.balanced
      rw [hz, zero_mul] at hb
      have hc := Fintype.card_pos (α := C)
      omega
    exact_mod_cast hn
  unfold macCost
  rw [← M.balanced]
  push_cast
  rw [show (S₁.bound : ℚ)*S₂.bound*M.fiber = (M.fiber : ℚ)*((S₁.bound : ℚ)*S₂.bound) by ring]
  exact mul_div_mul_left _ _ hf

theorem maxBudget_div_eq : maxBudget S₁ S₂ M/Fintype.card C = coefficient (Fmac := Fmac) S₁ S₂ := by
  unfold maxBudget coefficient
  rw [← max_div_div_right (Nat.cast_nonneg _), ← max_div_div_right (Nat.cast_nonneg _),
    ← max_div_div_right (Nat.cast_nonneg _), macBudget_div_eq,
    Linear.Runtime.CompiledSide.maxBudget_div_eq, Linear.Runtime.CompiledSide.maxBudget_div_eq, add_div]

theorem slotBudget_sum_div_eq :
    (∑ i, slotBudget S₁ S₂ M i)/Fintype.card C = constant (Fmac := Fmac) S₁ S₂ := by
  rw [sum_slotBudget, add_div, add_div, macBudget_div_eq,
    Linear.Runtime.CompiledSide.slotBudget_sum_div_eq, Linear.Runtime.CompiledSide.slotBudget_sum_div_eq]
  rfl

theorem error_eq (N : ℕ) :
    (N*maxBudget S₁ S₂ M + ∑ i, slotBudget S₁ S₂ M i)/Fintype.card C =
      N*coefficient (Fmac := Fmac) S₁ S₂ + constant (Fmac := Fmac) S₁ S₂ := by
  rw [add_div, mul_div_assoc, maxBudget_div_eq, slotBudget_sum_div_eq]

end LfzkV2.Joint.Cost
