import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sampling without replacement

This file is native to `LigeroFamily` and depends only on finite combinatorics.
-/

namespace LigeroFamily

/-- The probability that a uniform `c`-subset of a `b`-element set lies in a
fixed `a`-element subset. -/
def hypergeometricRatio (a b c : ℕ) : ℚ :=
  ((a.choose c : ℕ) : ℚ) / ((b.choose c : ℕ) : ℚ)

/-- Sampling without replacement is no worse than sampling with replacement. -/
theorem hypergeometricRatio_le_geometric (a b c : ℕ)
    (hab : a ≤ b) (hc : c ≤ b) (hb : 0 < b) :
    hypergeometricRatio a b c ≤ ((a : ℚ) / (b : ℚ)) ^ c := by
  unfold hypergeometricRatio
  induction c with
  | zero => simp
  | succ c ih =>
      by_cases hca : c + 1 ≤ a
      · have hcb : c + 1 ≤ b := hc
        have hc_a : c ≤ a := by omega
        have hc_b : c ≤ b := by omega
        have hb_c : 0 < b - c := by omega
        have hchooseB : (0 : ℚ) < (b.choose c : ℕ) := by
          exact_mod_cast Nat.choose_pos hc_b
        have hchooseBSucc : (0 : ℚ) < (b.choose (c + 1) : ℕ) := by
          exact_mod_cast Nat.choose_pos hcb
        have hcSucc : (0 : ℚ) < c + 1 := by positivity
        have hrecA :
            ((a.choose (c + 1) : ℕ) : ℚ) * (c + 1) =
              ((a.choose c : ℕ) : ℚ) * (a - c) := by
          exact_mod_cast Nat.choose_succ_right_eq a c
        have hrecB :
            ((b.choose (c + 1) : ℕ) : ℚ) * (c + 1) =
              ((b.choose c : ℕ) : ℚ) * (b - c) := by
          exact_mod_cast Nat.choose_succ_right_eq b c
        have hratio :
            ((a.choose (c + 1) : ℕ) : ℚ) /
                ((b.choose (c + 1) : ℕ) : ℚ) =
              (((a.choose c : ℕ) : ℚ) / ((b.choose c : ℕ) : ℚ)) *
                (((a - c : ℕ) : ℚ) / ((b - c : ℕ) : ℚ)) := by
          have ha_c : (0 : ℚ) < (a - c : ℕ) := by
            exact_mod_cast (show 0 < a - c by omega)
          rw [Nat.cast_sub hc_a, Nat.cast_sub hc_b]
          field_simp [ne_of_gt hchooseB, ne_of_gt hchooseBSucc,
            ne_of_gt hcSucc, ne_of_gt ha_c, ne_of_gt (show (0 : ℚ) < b - c by
              exact_mod_cast hb_c)]
          linear_combination
            (((b.choose (c + 1) : ℕ) : ℚ)) * hrecA -
              (((a.choose (c + 1) : ℕ) : ℚ)) * hrecB
        have hfactor :
            (((a - c : ℕ) : ℚ) / ((b - c : ℕ) : ℚ)) ≤
              (a : ℚ) / (b : ℚ) := by
          rw [div_le_div_iff₀ (by exact_mod_cast hb_c) (by exact_mod_cast hb)]
          rw [Nat.cast_sub hc_a, Nat.cast_sub hc_b]
          have hcab : (c : ℚ) * a ≤ c * b := by
            exact_mod_cast Nat.mul_le_mul_left c hab
          nlinarith
        rw [hratio, pow_succ]
        exact mul_le_mul (ih hc_b) hfactor (by positivity) (by positivity)
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
        positivity

/-- Opening one more coordinate cannot increase the probability that every
opened coordinate lies in a fixed subset. -/
theorem hypergeometricRatio_succ_le (a b c : ℕ)
    (hab : a ≤ b) (hc : c < b) :
    hypergeometricRatio a b (c + 1) ≤ hypergeometricRatio a b c := by
  unfold hypergeometricRatio
  by_cases hca : c + 1 ≤ a
  · have hc_a : c ≤ a := by omega
    have hc_b : c ≤ b := by omega
    have hchooseB : (0 : ℚ) < (b.choose c : ℕ) := by
      exact_mod_cast Nat.choose_pos hc_b
    have hchooseBSucc : (0 : ℚ) < (b.choose (c + 1) : ℕ) := by
      exact_mod_cast Nat.choose_pos (by omega : c + 1 ≤ b)
    have hcSucc : (0 : ℚ) < c + 1 := by positivity
    have hrecA :
        ((a.choose (c + 1) : ℕ) : ℚ) * (c + 1) =
          ((a.choose c : ℕ) : ℚ) * (a - c) := by
      exact_mod_cast Nat.choose_succ_right_eq a c
    have hrecB :
        ((b.choose (c + 1) : ℕ) : ℚ) * (c + 1) =
          ((b.choose c : ℕ) : ℚ) * (b - c) := by
      exact_mod_cast Nat.choose_succ_right_eq b c
    have hratio :
        ((a.choose (c + 1) : ℕ) : ℚ) /
            ((b.choose (c + 1) : ℕ) : ℚ) =
          (((a.choose c : ℕ) : ℚ) / ((b.choose c : ℕ) : ℚ)) *
            (((a - c : ℕ) : ℚ) / ((b - c : ℕ) : ℚ)) := by
      have ha_c : (0 : ℚ) < (a - c : ℕ) := by
        exact_mod_cast (show 0 < a - c by omega)
      rw [Nat.cast_sub hc_a, Nat.cast_sub hc_b]
      field_simp [ne_of_gt hchooseB, ne_of_gt hchooseBSucc,
        ne_of_gt hcSucc, ne_of_gt ha_c,
        ne_of_gt (show (0 : ℚ) < b - c by exact_mod_cast (by omega : 0 < b - c))]
      linear_combination
        (((b.choose (c + 1) : ℕ) : ℚ)) * hrecA -
          (((a.choose (c + 1) : ℕ) : ℚ)) * hrecB
    rw [hratio]
    apply mul_le_of_le_one_right (by positivity)
    rw [div_le_one (by exact_mod_cast (show 0 < b - c by omega))]
    exact_mod_cast Nat.sub_le_sub_right hab c
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
    positivity

theorem hypergeometricRatio_antitone_query (a b : ℕ) (hab : a ≤ b) :
    Antitone (hypergeometricRatio a b) := by
  apply antitone_nat_of_succ_le
  intro c
  by_cases hc : c < b
  · exact hypergeometricRatio_succ_le a b c hab hc
  · by_cases heq : c = b
    · subst c
      unfold hypergeometricRatio
      rw [Nat.choose_eq_zero_of_lt (by omega : b < b + 1)]
      simp
    · have hbc : b < c := by omega
      unfold hypergeometricRatio
      rw [Nat.choose_eq_zero_of_lt (by omega : b < c + 1),
        Nat.choose_eq_zero_of_lt hbc]
      simp

end LigeroFamily
