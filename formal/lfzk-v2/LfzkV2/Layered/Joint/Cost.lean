import LfzkV2.Layered.Joint.Charges

/-! Reordering does not change the sum of local verifier costs. Merging the
opening roles does change their maximum: the one common query pays the sum
of the two residual budgets. -/

namespace LfzkV2.Layered.Joint.Cost

open Finset RecursivePolygero Bcs.TotalOracle Replay
open LfzkV2.Joint (Participant Family)
open scoped Classical

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Layered.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Layered.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Layered.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Layered.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

private def push {m n : ℕ} (map : Fin m → Fin n) (f : Fin m → ℚ) (i : Fin n) : ℚ :=
  ∑ j, if map j = i then f j else 0

private theorem push_at {m n : ℕ} (map : Fin m → Fin n) (hinj : Function.Injective map)
    (f : Fin m → ℚ) (j : Fin m) : push map f (map j) = f j := by
  unfold push
  simp only [hinj.eq_iff, sum_ite_eq', mem_univ, if_true]

private theorem push_off {m n : ℕ} (map : Fin m → Fin n) (f : Fin m → ℚ) (i : Fin n)
    (hoff : ∀ j, map j ≠ i) : push map f i = 0 := by
  unfold push
  simp only [hoff, if_false, sum_const_zero]

private theorem sum_push {m n : ℕ} (map : Fin m → Fin n) (f : Fin m → ℚ) :
    (∑ i, push map f i) = ∑ j, f j := by
  unfold push
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, if_true]

noncomputable def slotBudget (i : Fin (slots S₁ S₂)) : ℚ :=
  (if i.val = 0 then (S₁.bound*S₂.bound*M.fiber : ℕ) else 0) +
    push (firstIndex S₁ S₂) S₁.slotBudget i + push (secondIndex S₁ S₂) S₂.slotBudget i

theorem budgetOne_at (proof : Proof S₁ S₂) (i : Fin (slots S₁ S₂)) :
    Charges.budgetOne S₁ S₂ (hashInput S₁ S₂ proof i.val) =
      push (firstIndex S₁ S₂) S₁.slotBudget i := by
  by_cases h : ∃ j, firstIndex S₁ S₂ j = i
  · obtain ⟨j,rfl⟩ := h
    rw [push_at _ (firstIndex_injective S₁ S₂), Charges.budgetOne]
    change (match localOne S₁ S₂ (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j.val)) with
      | some x => S₁.budget x | none => 0) = _
    rw [localOne_at _ _ _ _ j.isLt]
    exact S₁.budget_hashInput _ j
  · have hoff : ∀ j, firstIndex S₁ S₂ j ≠ i := by simpa only [not_exists] using h
    rw [push_off _ _ _ hoff, Charges.budgetOne, localOne_none_off]
    intro j he
    apply hoff j
    apply Fin.ext
    exact he.trans (slot_hashInput S₁ S₂ proof i.val i.isLt)

theorem budgetTwo_at (proof : Proof S₁ S₂) (i : Fin (slots S₁ S₂)) :
    Charges.budgetTwo S₁ S₂ (hashInput S₁ S₂ proof i.val) =
      push (secondIndex S₁ S₂) S₂.slotBudget i := by
  by_cases h : ∃ j, secondIndex S₁ S₂ j = i
  · obtain ⟨j,rfl⟩ := h
    rw [push_at _ (secondIndex_injective S₁ S₂), Charges.budgetTwo]
    change (match localTwo S₁ S₂ (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j.val)) with
      | some x => S₂.budget x | none => 0) = _
    rw [localTwo_at _ _ _ _ j.isLt]
    exact S₂.budget_hashInput _ j
  · have hoff : ∀ j, secondIndex S₁ S₂ j ≠ i := by simpa only [not_exists] using h
    rw [push_off _ _ _ hoff, Charges.budgetTwo, localTwo_none_off]
    intro j he
    apply hoff j
    apply Fin.ext
    exact he.trans (slot_hashInput S₁ S₂ proof i.val i.isLt)

theorem budget_hashInput (proof : Proof S₁ S₂) (i : Fin (slots S₁ S₂)) :
    Charges.budget S₁ S₂ M (hashInput S₁ S₂ proof i.val) = slotBudget S₁ S₂ M i := by
  rw [Charges.budget, slot_hashInput _ _ _ _ i.isLt, budgetOne_at, budgetTwo_at]
  rfl

theorem sum_slotBudget : (∑ i, slotBudget S₁ S₂ M i) =
    (S₁.bound*S₂.bound*M.fiber : ℕ) + (∑ j, S₁.slotBudget j) + ∑ j, S₂.slotBudget j := by
  unfold slotBudget
  rw [sum_add_distrib, sum_add_distrib, sum_push, sum_push]
  congr 2
  let zero : Fin (slots S₁ S₂) := ⟨0,by unfold slots; omega⟩
  have h : ∀ i : Fin (slots S₁ S₂), i.val = 0 ↔ i = zero := by
    intro i
    exact ⟨fun he => Fin.ext he, fun he => congrArg Fin.val he⟩
  simp only [h, Nat.cast_ite, Nat.cast_zero, sum_ite_eq', mem_univ, if_true]

noncomputable def maxBudget : ℚ :=
  max (S₁.bound*S₂.bound*M.fiber : ℕ)
    (max (max S₁.maxBudget S₂.maxBudget) (S₁.potential.queryBudget+S₂.potential.queryBudget))

theorem maxBudget_nonneg : 0 ≤ maxBudget S₁ S₂ M :=
  (Nat.cast_nonneg _).trans (le_max_left _ _)

theorem budgetOne_le (p : Domain S₁ S₂) : Charges.budgetOne S₁ S₂ p ≤ S₁.maxBudget := by
  unfold Charges.budgetOne
  split
  · exact S₁.budget_le_max _
  · exact S₁.maxBudget_nonneg

theorem budgetTwo_le (p : Domain S₁ S₂) : Charges.budgetTwo S₁ S₂ p ≤ S₂.maxBudget := by
  unfold Charges.budgetTwo
  split
  · exact S₂.budget_le_max _
  · exact S₂.maxBudget_nonneg

theorem budgetOne_opening_le (p : Domain S₁ S₂)
    (h : (points S₁ S₂).slot p = backendStart S₁ S₂+2) :
    Charges.budgetOne S₁ S₂ p ≤ S₁.potential.queryBudget := by
  unfold Charges.budgetOne localOne
  rw [h, if_neg (by unfold backendStart; omega), if_neg (by omega), if_pos rfl]
  cases hf : statementsAt S₁ S₂ p <;> cases hc : current S₁ S₂ p <;>
    simp [Layered.Runtime.CompiledSide.budget, Layered.Runtime.FiatShamir.budget,
      Layered.Runtime.Replay.opening, S₁.potential.queryBudget_nonneg]

theorem budgetTwo_opening_le (p : Domain S₁ S₂)
    (h : (points S₁ S₂).slot p = backendStart S₁ S₂+2) :
    Charges.budgetTwo S₁ S₂ p ≤ S₂.potential.queryBudget := by
  unfold Charges.budgetTwo localTwo
  rw [h, if_neg (by omega), if_neg (by omega), if_pos rfl]
  cases hf : statementsAt S₁ S₂ p <;> cases hc : current S₁ S₂ p <;>
    simp [Layered.Runtime.CompiledSide.budget, Layered.Runtime.FiatShamir.budget,
      Layered.Runtime.Replay.opening, S₂.potential.queryBudget_nonneg]

theorem budget_le_max (p : Domain S₁ S₂) : Charges.budget S₁ S₂ M p ≤ maxBudget S₁ S₂ M := by
  have hmaxOne : S₁.maxBudget ≤ maxBudget S₁ S₂ M :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hmaxTwo : S₂.maxBudget ≤ maxBudget S₁ S₂ M :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  by_cases hzero : (points S₁ S₂).slot p = 0
  · have hOne : localOne S₁ S₂ p = none := by
      unfold localOne
      rw [hzero]
      simp only [lt_self_iff_false, false_and, if_false,
        if_neg (by unfold backendStart secondStart; omega : 0 ≠ backendStart S₁ S₂),
        if_neg (by omega : 0 ≠ backendStart S₁ S₂+2)]
    have hTwo : localTwo S₁ S₂ p = none := by
      unfold localTwo
      rw [hzero, if_neg (by unfold secondStart; omega), if_neg (by omega), if_neg (by omega)]
    simp only [Charges.budget, hzero, if_true, Charges.budgetOne, Charges.budgetTwo,
      hOne, hTwo, add_zero]
    exact le_max_left _ _
  · by_cases hopen : (points S₁ S₂).slot p = backendStart S₁ S₂+2
    · simp only [Charges.budget, if_neg hzero, Nat.cast_zero, zero_add]
      exact (add_le_add (budgetOne_opening_le S₁ S₂ p hopen) (budgetTwo_opening_le S₁ S₂ p hopen)).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    · by_cases hfirst : (0 < (points S₁ S₂).slot p ∧ (points S₁ S₂).slot p < secondStart S₁) ∨
          (points S₁ S₂).slot p = backendStart S₁ S₂
      · have hTwo : localTwo S₁ S₂ p = none := by
          unfold localTwo
          rw [if_neg (by rcases hfirst with h | h <;> omega),
            if_neg (by rcases hfirst with h | h <;> unfold backendStart at * <;> omega), if_neg hopen]
        simp only [Charges.budget, if_neg hzero, Nat.cast_zero, zero_add,
          Charges.budgetTwo, hTwo, add_zero]
        exact (budgetOne_le S₁ S₂ p).trans hmaxOne
      · have hOne : localOne S₁ S₂ p = none := by
          unfold localOne
          rw [if_neg (by tauto), if_neg (by tauto), if_neg hopen]
        simp only [Charges.budget, if_neg hzero, Nat.cast_zero, zero_add,
          Charges.budgetOne, hOne, zero_add]
        exact (budgetTwo_le S₁ S₂ p).trans hmaxTwo

end LfzkV2.Layered.Joint.Cost
