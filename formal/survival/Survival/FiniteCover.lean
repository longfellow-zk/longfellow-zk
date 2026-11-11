import Bcs.ProbabilityBounds
import Mathlib.Tactic.Linarith

/-! Combine a stopped monitor's probability law with global charge means.
The hash exception is retained symbolically until sampler averaging. -/
noncomputable section
namespace Survival.FiniteCover
open Finset Bcs.FiniteProbability
open scoped Classical

theorem density_indicator {Omega : Type} [Fintype Omega] (event : Omega → Prop) :
    density event = (∑ x : Omega, if event x then (1 : ℚ) else 0) / Fintype.card Omega := by
  unfold density
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]

/-- Central deterministic cover: an accepted failure is paid by the raw
exception, the first transparent escape, or the retained nonnegative cost. -/
theorem indicator_cover {Omega : Type} (failed exception escaped : Omega → Prop)
    (cost : Omega → ℚ) (nonnegative : ∀ h, 0 ≤ cost h)
    (cover : ∀ h, failed h → ¬exception h → escaped h ∨ 1 ≤ cost h) (h : Omega) :
    (if failed h then (1 : ℚ) else 0) ≤
      (if exception h then 1 else 0) + (if escaped h then 1 else 0) + cost h := by
  by_cases bad : failed h <;> by_cases hash : exception h <;> by_cases escape : escaped h <;>
    simp only [bad, hash, escape, if_true, if_false] <;>
    first | linarith [nonnegative h] | simpa only [zero_add] using (cover h bad hash).resolve_left escape

/-- Integrate the same pointwise cover before choosing a linear or saturated
query-budget estimate. The charge mean is unconditional on eventual safety. -/
theorem expectation_cover {Omega : Type} [Fintype Omega]
    (failed exception escaped : Omega → Prop) (cost : Omega → ℚ)
    (nonnegative : ∀ h, 0 ≤ cost h)
    (cover : ∀ h, failed h → ¬exception h → escaped h ∨ 1 ≤ cost h) :
    density failed ≤ density exception + density escaped +
      (∑ h, cost h) / Fintype.card Omega := by
  rw [density_indicator, density_indicator, density_indicator, ← add_div, ← add_div,
    ← sum_add_distrib, ← sum_add_distrib]
  exact div_le_div_of_nonneg_right
    (sum_le_sum fun h _ => indicator_cover failed exception escaped cost nonnegative cover h)
    (Nat.cast_nonneg _)

theorem failure_le {Omega : Type} [Fintype Omega]
    (failed hash escaped : Omega → Prop) (count : Omega → ℕ) (cost : Omega → ℚ)
    (allowance cap : ℚ)
    (nonnegative : ∀ h, 0 ≤ cost h)
    (cover : ∀ h, failed h → ¬hash h → escaped h ∨ 1 ≤ cost h)
    (cost_mean : (∑ h, cost h)/Fintype.card Omega ≤
      allowance*((∑ h, (count h : ℚ))/Fintype.card Omega))
    (law : density escaped + allowance*((∑ h, (count h : ℚ))/Fintype.card Omega) ≤ cap) :
    density failed ≤ cap + density hash := by
  have integrated := expectation_cover failed hash escaped cost nonnegative cover
  linarith

end Survival.FiniteCover
