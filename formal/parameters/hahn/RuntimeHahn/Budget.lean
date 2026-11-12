import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Field-aware per-query budgets, independent of either commitment protocol.
MLDSA uses its actual sextic field size and reserves both the rank and scalar
batching field terms before assigning the remaining budget to Hahn excess. -/
namespace RuntimeHahn

inductive Budget where
  | universal
  | mldsa128

namespace Budget

def minimumField : Budget → ℕ
  | .universal => 2^128
  | .mldsa128 => 8380417^6

def rankDivisor : Budget → ℕ
  | .universal => 4
  | .mldsa128 => 1

def threshold : Budget → ℚ
  | .universal => 1 / 2^130
  | .mldsa128 => 1 / 2^128 - 2 / (minimumField .mldsa128 : ℚ)

def rankBudget (b : Budget) : ℚ := 1 / ((b.rankDivisor : ℚ)*b.minimumField)
def additiveBudget (b : Budget) : ℚ := b.threshold+b.rankBudget

theorem field_pos (b : Budget) : 0 < b.minimumField := by cases b <;> norm_num [minimumField]
theorem threshold_nonneg (b : Budget) : 0 ≤ b.threshold := by cases b <;> norm_num [threshold,minimumField]
theorem threshold_le_one (b : Budget) : b.threshold ≤ 1 := by cases b <;> norm_num [threshold,minimumField]
theorem threshold_lt_one (b : Budget) : b.threshold < 1 := by cases b <;> norm_num [threshold,minimumField]
theorem field_error_lt_one (b : Budget) : b.rankBudget+1/(b.minimumField : ℚ) < 1 := by
  cases b <;> norm_num [rankBudget,rankDivisor,minimumField]

def rankError (n k s q : ℕ) : ℚ := (n.choose (k+s+s+1) : ℚ)/(q : ℚ)^(s+1)

/-- The rank union bound and the small-rank FS side condition, without rounding. -/
theorem rank_bounds (b : Budget) {n k s q : ℕ}
    (hnum : (n.choose (k+s+s+1) : ℚ) ≤ (b.minimumField : ℚ)^s/b.rankDivisor)
    (hq : b.minimumField ≤ q) :
    rankError n k s q ≤ b.rankBudget ∧ rankError n k s q ≤ 1/(q : ℚ) := by
  have hm : (0 : ℚ) < b.minimumField := by exact_mod_cast b.field_pos
  have hq0 : (0 : ℚ) < q := hm.trans_le (by exact_mod_cast hq)
  have hqmin : (b.minimumField : ℚ) ≤ q := by exact_mod_cast hq
  have hd : (0 : ℚ) < b.rankDivisor := by cases b <;> norm_num [rankDivisor]
  have hp : (b.minimumField : ℚ)^s ≤ (q : ℚ)^s := pow_le_pow_left₀ hm.le hqmin _
  have hc : (n.choose (k+s+s+1) : ℚ)/(q : ℚ)^s ≤ 1/b.rankDivisor := by
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    have h := hnum.trans (div_le_div_of_nonneg_right hp hd.le)
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using h
  have hr : rankError n k s q ≤ (1/(b.rankDivisor : ℚ))/(q : ℚ) := by
    unfold rankError
    rw [pow_succ,div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hc hq0.le
  constructor
  · apply hr.trans
    have h := div_le_div_of_nonneg_left (show (0:ℚ) ≤ 1/b.rankDivisor by positivity) hm hqmin
    simpa only [rankBudget,div_mul_eq_div_div] using h
  · have hd1 : (1 : ℚ)/b.rankDivisor ≤ 1 := by cases b <;> norm_num [rankDivisor]
    exact hr.trans (div_le_div_of_nonneg_right hd1 hq0.le)

theorem additiveBudget_universal : additiveBudget .universal = 1/2^129 := by
  norm_num [additiveBudget,threshold,rankBudget,rankDivisor,minimumField]

/-- MLDSA's complete coefficient, including both field terms, is at most 2^-128. -/
theorem mldsa_per_query {q : ℕ} (hq : minimumField .mldsa128 ≤ q) :
    1/(q : ℚ)+additiveBudget .mldsa128 ≤ 1/2^128 := by
  have hm : (0 : ℚ) < minimumField .mldsa128 := by norm_num [minimumField]
  have hi : 1/(q : ℚ) ≤ 1/(minimumField .mldsa128 : ℚ) :=
    div_le_div_of_nonneg_left (by norm_num) hm (by exact_mod_cast hq)
  have he : 1/(minimumField .mldsa128 : ℚ)+additiveBudget .mldsa128 = (1:ℚ)/2^128 := by
    norm_num [additiveBudget,threshold,rankBudget,rankDivisor,minimumField]
  linarith

/-- Every retained runtime profile has a coefficient at most 2^-127 before
the separate commitment-binding error is added. -/
theorem per_query_le_127 (b : Budget) {q : ℕ} (hq : b.minimumField ≤ q) :
    1/(q : ℚ)+b.additiveBudget ≤ 1/2^127 := by
  cases b with
  | universal =>
    rw [additiveBudget_universal]
    have hi : 1/(q : ℚ) ≤ 1/(2^128 : ℚ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hq)
    have hn : (1/(2^128 : ℚ)+1/2^129) ≤ 1/2^127 := by norm_num
    linarith
  | mldsa128 => exact (mldsa_per_query hq).trans (by norm_num)

end Budget
end RuntimeHahn
