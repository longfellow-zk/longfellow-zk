import Survival.Hybrid
import Mathlib.Algebra.Order.Ring.Pow

/-! Elementary uniform survival margin, without real logarithms or limits.
Eight blocks and Bernoulli's inequality suffice even for enormous budgets.
-/
namespace Survival.Parameters

theorem survival_third (rate : ℚ) (nonnegative : 0 ≤ rate)
    (small : rate ≤ 1/1024) (fuel : ℕ) (budget : rate*fuel ≤ 1) :
    (1/3 : ℚ) ≤ (1-rate)^fuel := by
  let block : ℕ := fuel/8+1
  have covered : fuel ≤ 8*block := by dsimp [block]; omega
  have quotient : 8*(fuel/8) ≤ fuel := Nat.mul_div_le fuel 8
  have castQuotient : (8 : ℚ)*(fuel/8 : ℕ) ≤ fuel := by exact_mod_cast quotient
  have blockBound : (block : ℚ)*rate ≤ 1/8+rate := by
    have weighted := mul_le_mul_of_nonneg_right castQuotient nonnegative
    dsimp [block]
    push_cast
    nlinarith
  have bernoulli := one_add_mul_le_pow (show (-2 : ℚ) ≤ -rate by linarith) block
  have lower : (895/1024 : ℚ) ≤ (1-rate)^block := by
    change 1+(block : ℚ)*(-rate) ≤ (1+-rate)^block at bernoulli
    simp only [← sub_eq_add_neg] at bernoulli
    linarith
  have powers := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 895/1024) lower 8
  have order := pow_le_pow_of_le_one (show (0 : ℚ) ≤ 1-rate by linarith)
    (show 1-rate ≤ 1 by linarith) covered
  have exactMargin : (1/3 : ℚ) ≤ (895/1024)^8 := by norm_num
  rw [← pow_mul, Nat.mul_comm block 8] at powers
  exact exactMargin.trans (powers.trans order)

theorem hybrid_margin (rate opaqueFraction correction : ℚ) (nonnegative : 0 ≤ rate)
    (small : rate ≤ 1/1024) (hl : 0 ≤ opaqueFraction) (hl51 : opaqueFraction ≤ 51/100)
    (fuel : ℕ) (budget : rate*fuel ≤ 1) (hash : correction ≤ 1/8) :
    Hybrid.envelope rate opaqueFraction fuel+correction ≤ 577/600 :=
  Hybrid.nonvacuous_of_survival rate opaqueFraction correction hl hl51 fuel budget
    (survival_third rate nonnegative small fuel budget) hash

end Survival.Parameters
