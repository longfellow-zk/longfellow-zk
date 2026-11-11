import polygero.Algebra.FiniteProbability
import Mathlib.Tactic.Ring

namespace RecursivePolygero.NonrecursiveFS.Balance
open Finset
open scoped Classical
/-- A balanced decoder's fiber count can be removed from a nonnegative
clipped local budget, even when the un-clipped rational expression has an
unknown sign.  This gives a context-independent hash-answer budget. -/
theorem max_zero_nat_mul_le
    {a b : ℕ} (hab : a ≤ b) (x : ℚ) :
    max 0 ((a : ℚ) * x) ≤ max 0 ((b : ℚ) * x) := by
  apply max_le
  · exact le_max_left _ _
  · by_cases hx : 0 ≤ x
    · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hx).trans
        (le_max_right _ _)
    · have hax : (a : ℚ) * x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_ge hx)
      exact hax.trans (le_max_left _ _)

theorem decoded_weight_sum_le
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (decode : C → X) (weight : X → ℚ)
    (hnonneg : ∀ x, 0 ≤ weight x)
    (k : ℕ)
    (hbalance : ∀ x,
      (univ.filter fun c : C => decode c = x).card ≤ k) :
    ∑ c : C, weight (decode c) ≤ k * ∑ x : X, weight x := by
  classical
  have hfiber (x : X) :
      (∑ c : C, if decode c = x then weight x else 0) =
        ((univ.filter fun c : C => decode c = x).card : ℚ) * weight x := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ c : C, weight (decode c)) =
        ∑ c : C, ∑ x : X, if decode c = x then weight x else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          simp
    _ = ∑ x : X, ∑ c : C,
          if decode c = x then weight x else 0 := Finset.sum_comm
    _ = ∑ x : X,
          ((univ.filter fun c : C => decode c = x).card : ℚ) * weight x := by
          apply Finset.sum_congr rfl
          intro x _
          exact hfiber x
    _ ≤ ∑ x : X, (k : ℚ) * weight x := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hbalance x) (hnonneg x)
    _ = k * ∑ x : X, weight x := by rw [Finset.mul_sum]

/-- Convert a uniform challenge expectation into the exact local hash-answer
budget, retaining the decoder's fiber factor. -/
theorem decoded_mean_le
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X] [Nonempty X]
    (decode : C → X) (weight : X → ℚ)
    (hnonneg : ∀ x, 0 ≤ weight x)
    (k : ℕ)
    (hbalance : ∀ x,
      (univ.filter fun c : C => decode c = x).card ≤ k)
    (bound : ℚ)
    (hmean : (∑ x : X, weight x) / Fintype.card X ≤ bound) :
    ∑ c : C, weight (decode c) ≤
      k * Fintype.card X * bound := by
  have hx : (0 : ℚ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ x : X, weight x) ≤ Fintype.card X * bound := by
    simpa only [mul_comm] using (div_le_iff₀ hx).mp hmean
  calc
    (∑ c : C, weight (decode c)) ≤
        k * ∑ x : X, weight x :=
          decoded_weight_sum_le decode weight hnonneg k hbalance
    _ ≤ k * (Fintype.card X * bound) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = k * Fintype.card X * bound := by ring

end RecursivePolygero.NonrecursiveFS.Balance
