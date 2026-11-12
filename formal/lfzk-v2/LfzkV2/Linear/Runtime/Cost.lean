import LfzkV2.Linear.Runtime.TwoFieldFS

/-! Normalize the actual staged verifier charges by the raw oracle alphabet.
The extra packing stage contributes one inverse-field term, independently of
the number of coordinates in a packed word. The direct side pays none. -/

namespace LfzkV2.Linear.Runtime

open Finset RecursivePolygero

private theorem balanced_mul_div {fiber q c : ℕ} (h : fiber*q = c) (hc : 0 < c) (v : ℚ) :
    (fiber : ℚ)*v/c = v/q := by
  have hf : (fiber : ℚ) ≠ 0 := by
    have hn : fiber ≠ 0 := by intro hz; rw [hz, zero_mul] at h; omega
    exact_mod_cast hn
  rw [← h, Nat.cast_mul]
  exact mul_div_mul_left v (q : ℚ) hf

namespace CompiledSide

variable {F C Context : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype C] [Nonempty C] {out input : ℕ}
variable {circuit : Native.Circuit F out input} {I : Instance F}
variable (S : CompiledSide F C Context circuit I)

noncomputable def packingRate : ℚ :=
  (if S.packed then S.packingBudget else 0)/Fintype.card C

noncomputable def coefficient : ℚ :=
  max ((S.bound : ℚ)*max ((max out 2 : ℕ)/(Fintype.card F : ℚ))
    (2/((Fintype.card F-1 : ℕ) : ℚ)))
    (max S.packingRate
      (max (S.potential.challengeBudget/Fintype.card C) (S.potential.queryBudget/Fintype.card C)))

noncomputable def constant : ℚ :=
  (S.bound : ℚ)*((out+circuit.sharpLayerBudget)/Fintype.card F +
    (2*circuit.layers : ℕ)/((Fintype.card F-1 : ℕ) : ℚ)) + S.packingRate +
    S.potential.challengeBudget/Fintype.card C + S.potential.queryBudget/Fintype.card C

theorem maxBudget_div_eq : S.maxBudget/Fintype.card C = S.coefficient := by
  unfold maxBudget FiatShamir.maxBudget coefficient packingRate
  rw [← max_div_div_right (Nat.cast_nonneg _), ← max_div_div_right (Nat.cast_nonneg _),
    ← max_div_div_right (Nat.cast_nonneg _)]
  congr 1
  rw [Nat.cast_mul, mul_div_assoc, S.sampling.max_rate]

theorem slotBudget_sum_div_eq :
    (∑ i, S.slotBudget i)/Fintype.card C = S.constant := by
  change (∑ i, FiatShamir.slotBudget (bound := S.bound) circuit I S.sampling S.packed
    S.packingBudget S.potential i)/Fintype.card C = _
  rw [FiatShamir.slotBudget_sum, add_div, add_div, add_div]
  unfold constant packingRate
  congr 3
  rw [Nat.cast_mul, mul_div_assoc, Nat.cast_add, add_div,
    S.sampling.field_rate, S.sampling.terminal_rate]
  push_cast
  rfl

omit [Nonempty C] in
theorem direct_packingRate (hpacked : S.packed = false) : S.packingRate = 0 := by
  simp [packingRate, hpacked]

theorem packingRate_eq (hpacked : S.packed = true)
    (hbudget : S.packingBudget = (S.sampling.fieldFiber : ℚ)*S.bound) :
    S.packingRate = (S.bound : ℚ)/Fintype.card F := by
  simp only [packingRate, hpacked, ↓reduceIte, hbudget]
  exact balanced_mul_div S.sampling.balanced Fintype.card_pos _

end CompiledSide

namespace TwoFieldFS

open TwoFieldReplay

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C] [Nonempty C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

noncomputable def macCost : ℚ := (S₁.bound : ℚ)*S₂.bound/Fintype.card Fmac

noncomputable def coefficient : ℚ :=
  max (macCost (Fmac := Fmac) S₁ S₂) (max S₁.coefficient S₂.coefficient)

noncomputable def constant : ℚ :=
  macCost (Fmac := Fmac) S₁ S₂ + S₁.constant + S₂.constant

theorem macBudget_div_eq :
    ((S₁.bound*S₂.bound*M.fiber : ℕ) : ℚ)/Fintype.card C =
      macCost (Fmac := Fmac) S₁ S₂ := by
  unfold macCost
  push_cast
  rw [show (S₁.bound : ℚ)*S₂.bound*M.fiber = (M.fiber : ℚ)*((S₁.bound : ℚ)*S₂.bound) by ring]
  exact balanced_mul_div M.balanced Fintype.card_pos _

theorem maxBudget_div_eq :
    maxBudget S₁ S₂ M/Fintype.card C = coefficient (Fmac := Fmac) S₁ S₂ := by
  unfold maxBudget coefficient
  rw [← max_div_div_right (Nat.cast_nonneg _), ← max_div_div_right (Nat.cast_nonneg _),
    macBudget_div_eq, CompiledSide.maxBudget_div_eq, CompiledSide.maxBudget_div_eq]

omit [Nonempty C] in
theorem slotBudget_sum (proof : Proof S₁ S₂) :
    (∑ i, slotBudget S₁ S₂ M i) =
      (S₁.bound*S₂.bound*M.fiber : ℕ) + (∑ i, S₁.slotBudget i) + (∑ i, S₂.slotBudget i) := by
  calc
    _ = ∑ i : Fin (slots S₁ S₂),
        TwoFieldPotential.budget S₁ S₂ M (hashInput S₁ S₂ proof i.val) := by
      apply sum_congr rfl
      intro i _
      exact (budget_hashInput S₁ S₂ M proof i).symm
    _ = _ := by
      rw [TwoFieldReplay.sum_hashInput]
      simp only [TwoFieldPotential.budget, S₁.budget_hashInput, S₂.budget_hashInput]

theorem slotBudget_sum_div_eq (proof : Proof S₁ S₂) :
    (∑ i, slotBudget S₁ S₂ M i)/Fintype.card C = constant (Fmac := Fmac) S₁ S₂ := by
  rw [slotBudget_sum S₁ S₂ M proof, add_div, add_div, macBudget_div_eq,
    CompiledSide.slotBudget_sum_div_eq, CompiledSide.slotBudget_sum_div_eq]
  rfl

theorem error_eq (N : ℕ) (proof : Proof S₁ S₂) :
    (N*maxBudget S₁ S₂ M + ∑ i, slotBudget S₁ S₂ M i)/Fintype.card C =
      N*coefficient (Fmac := Fmac) S₁ S₂ + constant (Fmac := Fmac) S₁ S₂ := by
  rw [add_div, mul_div_assoc, maxBudget_div_eq, slotBudget_sum_div_eq S₁ S₂ M proof]

end TwoFieldFS
end LfzkV2.Linear.Runtime
