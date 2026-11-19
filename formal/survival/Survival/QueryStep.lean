import Survival.FiniteCover

/-! One fresh-answer query step is either a transparent local test or an opaque
charged step. This abstraction concerns the adversary's queries, so it also
covers adaptive choices of protocol roles and queries outside the final path.
-/
noncomputable section
namespace Survival
open Finset Bcs.FiniteProbability
open scoped Classical

structure QueryStep (A : Type) where
  marked : Bool
  safe : A → Prop
  opaque_safe : marked = true → ∀ answer, safe answer

namespace QueryStep
variable {A : Type} [Fintype A] [Nonempty A]

def ofCharge (marked : Bool) (charge : A → ℚ) : QueryStep A where
  marked := marked
  safe answer := marked = true ∨ charge answer < 1
  opaque_safe marked _ := Or.inl marked

theorem charge_hazard (marked : Bool) (charge : A → ℚ) (rate : ℚ)
    (nonnegative : ∀ answer, 0 ≤ charge answer)
    (mean : (∑ answer, charge answer) ≤ Fintype.card A * rate) :
    density (fun answer => ¬(ofCharge marked charge).safe answer) ≤ rate := by
  apply (Bcs.FiniteProbability.density_le_mean _ charge nonnegative ?_).trans
  · apply (div_le_iff₀ (by positivity : (0 : ℚ) < Fintype.card A)).mpr
    simpa only [mul_comm] using mean
  · intro answer bad
    exact le_of_not_gt (fun small => bad (Or.inr small))

private theorem mean_test (test : A → Prop) (value : ℚ) :
    (∑ answer : A, if test answer then value else 1) / Fintype.card A =
      value+(1-value)*density (fun answer => ¬test answer) := by
  have pointwise (answer : A) : (if test answer then value else (1 : ℚ)) =
      value+(1-value)*(if ¬test answer then 1 else 0) := by
    by_cases h : test answer <;> simp [h]
  simp_rw [pointwise]
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum,
    add_div]
  simp only [mul_div_assoc]
  rw [FiniteCover.density_indicator]
  have nonzero : (Fintype.card A : ℚ) ≠ 0 := by positivity
  field_simp
  congr 2
  apply sum_congr rfl
  intro answer _
  by_cases h : test answer <;> simp [h]

/-- A single potential argument handles every transparent protocol test and
an opaque Polygero/hash allowance. No hazard is required at an opaque query step. -/
theorem step_le (step : QueryStep A) (rate allowance value cap : ℚ)
    (bounded : value ≤ 1)
    (hazard : step.marked = false → density (fun answer => ¬step.safe answer) ≤ rate)
    (transparent_step : rate+(1-rate)*value ≤ cap) (opaque_step : allowance+value ≤ cap)
    (continuation : A → ℚ) (tail_bound : ∀ answer, continuation answer ≤ value) :
    (if step.marked then allowance else 0) +
      (∑ answer : A, if step.safe answer then continuation answer else 1)/Fintype.card A ≤ cap := by
  have averaged := div_le_div_of_nonneg_right (sum_le_sum (s := univ) (fun answer _ =>
    show (if step.safe answer then continuation answer else 1) ≤
      (if step.safe answer then value else 1) from by split_ifs; exact tail_bound answer; exact le_rfl))
    (show (0 : ℚ) ≤ Fintype.card A by positivity)
  rw [mean_test] at averaged
  cases marked : step.marked with
  | false =>
      have scaled := mul_le_mul_of_nonneg_left (hazard marked) (sub_nonneg.mpr bounded)
      simp only [Bool.false_eq_true, if_false, zero_add]
      linarith
  | true =>
      have zero : density (fun answer => ¬step.safe answer) = 0 := by
        simp [density, step.opaque_safe marked]
      rw [zero, mul_zero, add_zero] at averaged
      simp only [if_true]
      linarith

end QueryStep
end Survival
