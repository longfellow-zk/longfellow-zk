import Survival.StoppedSearch

/-! The leading shared-query bound, independent of saturation or any numeric
profile: transparent escapes spend p E[J], retained opaque cost spends b E[K],
and J+K≤Q with b≤p. Both costs cover failure through one pointwise indicator. -/
noncomputable section
namespace Survival.SharedBudget
open Finset Bcs.FiniteProbability
open scoped Classical

/-- Shared query accounting for the surrogate escape indicator and opaque
allowance, before the common deterministic cover is integrated. -/
theorem accounting_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (escaped : Omega → Prop) (transparent opaqueCount : Omega → ℕ)
    (rate allowance : ℚ) (queries : ℕ)
    (rate_nonnegative : 0 ≤ rate) (allowance_le : allowance ≤ rate)
    (slots : ∀ h, transparent h + opaqueCount h ≤ queries)
    (escape_mean : density escaped ≤ rate*((∑ h, (transparent h : ℚ))/Fintype.card Omega)) :
    density escaped + allowance*((∑ h, (opaqueCount h : ℚ))/Fintype.card Omega) ≤ rate*queries := by
  have opaque_nonnegative : (0 : ℚ) ≤ (∑ h, (opaqueCount h : ℚ))/Fintype.card Omega := by positivity
  have scaled := mul_le_mul_of_nonneg_right allowance_le opaque_nonnegative
  have counts := mean_le (fun h => (transparent h : ℚ) + (opaqueCount h : ℚ)) (queries : ℚ)
    (fun h => by exact_mod_cast slots h)
  rw [sum_add_distrib,add_div] at counts
  have budget := mul_le_mul_of_nonneg_left counts rate_nonnegative
  linarith

/-- One query budget pays both kinds of reached queries. No pQ≤1 premise. -/
theorem linear_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (failed exception escaped : Omega → Prop) (transparent opaqueCount : Omega → ℕ)
    (cost : Omega → ℚ) (rate allowance : ℚ) (queries : ℕ)
    (rate_nonnegative : 0 ≤ rate) (allowance_le : allowance ≤ rate)
    (nonnegative : ∀ h, 0 ≤ cost h)
    (cover : ∀ h, failed h → ¬exception h → escaped h ∨ 1 ≤ cost h)
    (slots : ∀ h, transparent h + opaqueCount h ≤ queries)
    (escape_mean : density escaped ≤ rate*((∑ h, (transparent h : ℚ))/Fintype.card Omega))
    (cost_mean : (∑ h, cost h)/Fintype.card Omega ≤
      allowance*((∑ h, (opaqueCount h : ℚ))/Fintype.card Omega)) :
    density failed ≤ density exception + rate*queries := by
  have integrated := FiniteCover.expectation_cover failed exception escaped cost nonnegative cover
  have accounting := accounting_le escaped transparent opaqueCount rate allowance queries
    rate_nonnegative allowance_le slots escape_mean
  linarith

end Survival.SharedBudget
