import LfzkV2.Layered.Runtime.CompiledSide
import LfzkV2.Layered.FrontendBound

/-! Normalize the actual staged verifier charges by the raw oracle alphabet.
The extra packing stage contributes one inverse-field term, independently of
the number of coordinates in a packed word. The direct side pays none. -/

namespace LfzkV2.Layered.Runtime

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
variable {circuit : Layered.Circuit F out input} {I : Instance F}
variable (S : CompiledSide F C Context circuit I)

noncomputable def packingRate : ℚ :=
  (if S.packed then S.packingBudget else 0)/Fintype.card C

noncomputable def coefficient : ℚ :=
  max ((S.bound : ℚ)*max ((2 : ℕ)/(Fintype.card F : ℚ))
    (2/((Fintype.card F-1 : ℕ) : ℚ)))
    (max S.packingRate
      (max (S.potential.challengeBudget/Fintype.card C) (S.potential.queryBudget/Fintype.card C)))

noncomputable def constant : ℚ :=
  (S.bound : ℚ)*((circuit.ordinaryBudget)/Fintype.card F +
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

omit [Nonempty C] in
theorem direct_packingRate (hpacked : S.packed = false) : S.packingRate = 0 := by
  simp [packingRate, hpacked]

theorem packingRate_eq (hpacked : S.packed = true)
    (hbudget : S.packingBudget = (S.sampling.fieldFiber : ℚ)*S.bound) :
    S.packingRate = (S.bound : ℚ)/Fintype.card F := by
  simp only [packingRate, hpacked, ↓reduceIte, hbudget]
  exact balanced_mul_div S.sampling.balanced Fintype.card_pos _

end CompiledSide

end LfzkV2.Layered.Runtime
