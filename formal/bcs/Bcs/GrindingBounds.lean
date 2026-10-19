import Bcs.TwoStageSearch

namespace Bcs.GrindingBounds
open Finset
open scoped BigOperators
/-- A finite Bonferroni lower bound avoids expanding a huge power. -/
theorem root_search_lower (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    n * x - (n.choose 2 : ℚ) * x^2 ≤ 1 - (1-x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hx1)
    have hn : 0 ≤ (n.choose 2 : ℚ) * x^3 := by positivity
    simp only [pow_succ] at ⊢
    rw [show (n+1).choose 2 = n + n.choose 2 by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]]
    push_cast
    nlinarith

/-- The positive binomial prefix bounds the failure tail by its reciprocal.
Only a short prefix is evaluated in the concrete certificate below. -/
theorem child_search_lower (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (m d : ℕ) (hd : d ≤ m) :
    1 - 1 / (∑ j ∈ range (d+1), (m.choose j : ℚ) * x^j) ≤ 1 - (1-x)^m := by
  let S : ℚ := ∑ j ∈ range (d+1), (m.choose j : ℚ) * x^j
  have hs1 : 1 ≤ S := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ range (d+1)) =>
      mul_nonneg (Nat.cast_nonneg (m.choose j)) (pow_nonneg hx0 j))
      (show 0 ∈ range (d+1) by simp)
    simpa only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] using h
  have hs : S ≤ (1+x)^m := by
    rw [add_comm (1 : ℚ) x, add_pow]
    simp only [one_pow, mul_one]
    change (∑ j ∈ range (d+1), (m.choose j : ℚ) * x^j) ≤ _
    simp_rw [mul_comm (x ^ _) (↑(m.choose _) : ℚ)]
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro j _ _
    positivity
  have htail : 0 ≤ (1-x)^m := pow_nonneg (sub_nonneg.mpr hx1) _
  have hm := mul_le_mul_of_nonneg_left hs htail
  have hbase : 0 ≤ (1-x)*(1+x) ∧ (1-x)*(1+x) ≤ 1 := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hx1) (by linarith)
    · nlinarith [sq_nonneg x]
  have hp : ((1-x)*(1+x))^m ≤ 1 := pow_le_one₀ hbase.1 hbase.2
  rw [mul_pow] at hp
  have hprod : (1-x)^m * S ≤ 1 := hm.trans hp
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) hs1
  have ht : (1-x)^m ≤ 1 / S := (le_div_iff₀ hS).mpr hprod
  change 1 - 1 / S ≤ _
  linarith


end Bcs.GrindingBounds
