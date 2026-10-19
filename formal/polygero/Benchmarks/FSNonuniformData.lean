import polygero.Benchmarks.FSStoppedSpectrum

/-! Exact affine majorants for the nonuniform fixed-81 spectrum.
These arithmetic certificates are separate from the actual system-family
assembly. Ordinary kernel reduction checks every integer support size. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace RecursivePolygero.Benchmarks.FSNonuniformData
open ProfileAnalysis.StoppedSpectrum

def rate : ℚ := (24/5) / FSTwoLevel.fieldSize
theorem rate_nonneg : 0 ≤ rate := by unfold rate; positivity
def baseline : ℚ := 6 * FSStoppedSpectrum.theta 81 2714
def shifted : ℚ := rate-baseline
def capacity (a : ℕ) : ℚ := (a.choose 81 : ℚ) / Nat.choose 8192 81
noncomputable def f (a : ℕ) : ℚ := price shifted (capacity a)
noncomputable def slope5 : ℚ := f 2917-f 2916
noncomputable def slope6 : ℚ := (f 2869-f 2714)/155
noncomputable def line5 (a : ℕ) : ℚ := f 2916 + slope5*((a : ℚ)-2916)
noncomputable def line6 (a : ℕ) : ℚ := f 2714 + slope6*((a : ℚ)-2714)

noncomputable def rangeValid (lo count : ℕ) : Bool :=
  (List.range' lo count).all (fun a => decide (f a ≤ line5 a ∧ f a ≤ line6 a))

/-- The affine inequalities include every possible actual high-system
column capacity, not just the supports at which the lines are tangent. -/
theorem checked_ranges : rangeValid 2714 239 = true := by
  simp only [rangeValid, line5, line6, slope5, slope6, f, price, shifted, rate,
    baseline, capacity, FSStoppedSpectrum.theta, FSTwoLevel.fieldSize,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem checked :
    0 < shifted ∧ 0 ≤ slope5 ∧ 0 ≤ slope6 ∧
    5*f 2916+slope5*(14582-5*2916) ≤ (479/100 : ℚ) ∧
    6*f 2714+slope6*(17080-6*2714) ≤ (479/100 : ℚ) ∧
    FSTwoLevel.rankError ≤ (1/100 : ℚ)/FSTwoLevel.fieldSize ∧
    1 ≤ line5 2953 ∧ 1 ≤ line6 2953 := by
  simp only [line5, line6, slope5, slope6, f, price, shifted, rate, baseline, capacity,
    FSStoppedSpectrum.theta, FSTwoLevel.fieldSize, FSTwoLevel.rankError,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem affine_majorants (a : ℕ) (ha : 2714 ≤ a) (_han : a ≤ 8192) :
    f a ≤ line5 a ∧ f a ≤ line6 a := by
  by_cases hsmall : a < 2953
  · have hm : a ∈ List.range' 2714 239 := by
      simp only [List.mem_range']
      exact ⟨a-2714, by omega, by omega⟩
    exact of_decide_eq_true ((List.all_eq_true.mp checked_ranges) a hm)
  · have hcast : (2953 : ℚ) ≤ a := by exact_mod_cast (show 2953 ≤ a by omega)
    have hp : f a ≤ 1 := price_le_one _ _ checked.1 (by unfold capacity; positivity)
    have hm5 : line5 2953 ≤ line5 a := by
      unfold line5
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hcast _) checked.2.1)
    have hm6 : line6 2953 ≤ line6 a := by
      unfold line6
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hcast _) checked.2.2.1)
    constructor
    · exact hp.trans (checked.2.2.2.2.2.2.1.trans hm5)
    · exact hp.trans (checked.2.2.2.2.2.2.2.trans hm6)

end RecursivePolygero.Benchmarks.FSNonuniformData
