import LfzkV1.SoundnessBudget125

/-! The v1 budget with a separate allowance for three typed proof-annotation queries. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.SoundnessBudget125

open LfzkV1.MerkleWork125

/-- If the three annotation lookups fit the fixed algebraic charge of `109 / q`,
their addition to the Merkle exception preserves the original work denominator. -/
theorem bound_of_annotation_charges {p : ℚ} {fc L N tA : ℕ}
    (hp1 : p ≤ 1) (hfc : fc ≤ 14000) (hL : L ≤ 1200)
    (hp : p ≤ (if 13 ≤ tA then (109 + N * (701 / 100)) / q else 0)
      + (adaptiveMerkleNumerator fc tA (L + (N + 3)) : ℚ) / q ^ 2) :
    p ≤ (1 + N + tA : ℚ) / 2 ^ 125 := by
  let T : ℚ := 1 + N + tA
  let A : ℚ := if 13 ≤ tA then 109 + N * (701 / 100) else 0
  let M : ℚ := adaptiveMerkleNumerator fc tA (L + (N + 3))
  have hT : 1 ≤ T := by
    dsimp [T]
    linarith [Nat.cast_nonneg (α := ℚ) N, Nat.cast_nonneg (α := ℚ) tA]
  have hq : 0 < q := by norm_num [q]
  have h125 : (2 ^ 125 : ℚ) = q / 8 := by norm_num [q]
  change p ≤ T / 2 ^ 125
  by_cases hlarge : q / 8 ≤ T
  · exact hp1.trans ((le_div_iff₀ (by positivity)).2 (by rw [one_mul, h125]; exact hlarge))
  have hm : M ≤ 6 * (T + 3) ^ 2 + 2 ^ 26 * (T + 3) := by
    have h := adaptiveMerkleNumerator_le_v7 fc L (N + 3) tA hfc hL
    rw [show 1 + (N + 3) + tA = 1 + N + tA + 3 by omega] at h
    dsimp [M, T]
    exact_mod_cast h
  have hm' : M ≤ (6 * T + 2 ^ 29) * T := by
    refine hm.trans ?_
    have h := mul_nonneg (show (0 : ℚ) ≤ 54 + 3 * 2 ^ 26 by norm_num) (sub_nonneg.2 hT)
    have h' := mul_nonneg (show (0 : ℚ) ≤ 2 ^ 29 - (90 + 4 * 2 ^ 26) by norm_num) (zero_le_one.trans hT)
    nlinarith only [h, h']
  have hmcap (ε : ℚ) (hε : 6 * T + 2 ^ 29 ≤ ε * q) : M / q ≤ ε * T := by
    apply (div_le_iff₀ hq).2
    exact hm'.trans (by
      simpa only [mul_right_comm] using mul_le_mul_of_nonneg_right hε (zero_le_one.trans hT))
  have ha (α : ℚ) (hα : 0 ≤ α)
      (hconst : 14 ≤ T → 109 + (701 / 100) * (T - 14) ≤ α * T) : A ≤ α * T := by
    by_cases h : 13 ≤ tA
    · have ht : (13 : ℚ) ≤ tA := by exact_mod_cast h
      have h14 : 14 ≤ T := by dsimp [T]; linarith [Nat.cast_nonneg (α := ℚ) N]
      have hc := hconst h14
      simp only [A, if_pos h]
      dsimp only [T] at hc
      linarith
    · simp only [A, if_neg h]
      exact mul_nonneg hα (zero_le_one.trans hT)
  have hsum : A + M / q ≤ 8 * T := by
    by_cases hs : T ≤ 64
    · have hmSmall := hmcap (1 / 100) (by
        have hbound : (6 * 64 + 2 ^ 29 : ℚ) ≤ (1 / 100) * q := by norm_num [q]
        linarith)
      have haSmall := ha (799 / 100) (by norm_num) (fun ht => by linarith)
      linarith
    · have hmLarge := hmcap (4 / 5) (by
        have hbound : 6 * (q / 8) + 2 ^ 29 ≤ (4 / 5) * q := by norm_num [q]
        linarith [le_of_lt (lt_of_not_ge hlarge)])
      have haLarge := ha (36 / 5) (by norm_num) (fun _ => by linarith [le_of_lt (lt_of_not_ge hs)])
      linarith
  have hscaled : p * q ≤ A + M / q := by
    have h := mul_le_mul_of_nonneg_right hp hq.le
    have cancel (x : ℚ) : x / q * q = x := by field_simp
    have cancelSq (x : ℚ) : x / q ^ 2 * q = x / q := by field_simp
    simpa only [add_mul, ite_mul, zero_mul, cancel, cancelSq, A, M] using h
  rw [h125, div_div_eq_mul_div, le_div_iff₀ hq]
  simpa only [mul_comm T 8] using hscaled.trans hsum

end LfzkV1.SoundnessBudget125
