import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic

namespace RecursivePolygero
open Finset
attribute [local instance] Classical.propDecidable

def mean {I : Type*} [Fintype I] (f : I → ℚ) : ℚ :=
  (∑ i, f i) / Fintype.card I

noncomputable def indicator (P : Prop) : ℚ := if P then 1 else 0

@[simp] theorem mean_const {I : Type*} [Fintype I] [Nonempty I] (c : ℚ) :
    mean (fun _ : I => c) = c := by
  have h : (Fintype.card I : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, h]

theorem mean_mono {I : Type*} [Fintype I] {f g : I → ℚ} (h : ∀ i, f i ≤ g i) :
    mean f ≤ mean g :=
  div_le_div_of_nonneg_right (sum_le_sum fun i _ => h i) (by positivity)

@[simp] theorem mean_add {I : Type*} [Fintype I] (f g : I → ℚ) :
    mean (fun i => f i + g i) = mean f + mean g := by simp [mean,sum_add_distrib,add_div]

theorem mean_sub {I : Type*} [Fintype I] (f g : I → ℚ) :
    mean (fun i => f i - g i) = mean f - mean g := by
  simp [mean, sum_sub_distrib, sub_div]

theorem mean_mul_left {I : Type*} [Fintype I] (c : ℚ) (f : I → ℚ) :
    mean (fun i => c * f i) = c * mean f := by
  simp [mean, ← mul_sum, mul_div_assoc]

/-- A count depending only on the second coordinate has the same normalized
sum over a product. No response is selected by this identity. -/
theorem mean_snd {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] (f : J → ℚ) :
    mean (fun ij : I × J => f ij.2) = mean f := by
  unfold mean
  simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast Fintype.card_ne_zero (α := I))

@[simp] theorem mean_indicator {I : Type*} [Fintype I] (P : I → Prop) :
    mean (fun i => indicator (P i)) = ((univ.filter P).card : ℚ) / Fintype.card I := by
  simp [mean,indicator]

theorem mean_le {I : Type*} [Fintype I] [Nonempty I] {f : I → ℚ} {b : ℚ}
    (h : ∀ i, f i ≤ b) : mean f ≤ b := by
  simpa using mean_mono h

/-- Partition a counted predicate into exceptional and surviving cases. -/
theorem indicator_le_split (P E : Prop) :
    indicator P ≤ indicator E+indicator (P ∧ ¬E) := by
  unfold indicator
  split_ifs <;> simp_all

theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num

end RecursivePolygero
