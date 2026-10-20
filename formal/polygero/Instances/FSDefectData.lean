import polygero.Instances.FSStoppedSpectrum

/-! Exact arithmetic for the defect-sensitive fixed-81 stopping price.
The recursive six-response baseline is included before pricing exceptions. -/

set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace RecursivePolygero.Instances.FSDefectData

open ProfileAnalysis.StoppedSpectrum

def rate : ℚ := 4 / FSTwoLevel.fieldSize
theorem rate_nonneg : 0 ≤ rate := by unfold rate; positivity
def baseline : ℚ := 6 * FSStoppedSpectrum.theta 81 2714
def shifted : ℚ := rate-baseline
def capacity (a : ℕ) : ℚ := (a.choose 81 : ℚ) / Nat.choose 8192 81
noncomputable def f (a : ℕ) : ℚ := price shifted (capacity a)
noncomputable def slope : ℚ := (f 2858-f 2714)/144
noncomputable def line (a : ℕ) : ℚ := f 2714 + slope*((a : ℚ)-2714)

noncomputable def rangeValid (lo count : ℕ) : Bool :=
  (List.range' lo count).all (fun a => decide (f a ≤ line a))

theorem checked_ranges : rangeValid 2714 180 = true := by
  simp only [rangeValid, line, slope, f, price, shifted, rate, baseline, capacity,
    FSStoppedSpectrum.theta, FSTwoLevel.fieldSize, Nat.choose_eq_fast_choose]
  decide +kernel

theorem checked :
    0 < shifted ∧ 2*shifted < 1 ∧ 0 ≤ slope ∧
    5*f 2714+slope*(14272-5*2714) ≤ (3999/1000 : ℚ) ∧
    6*f 2714+slope*(16992-6*2714) ≤ (3999/1000 : ℚ) ∧
    (3999/1000 : ℚ) ≤ 4-7/(FSTwoLevel.fieldSize : ℚ) ∧
    7/(FSTwoLevel.fieldSize : ℚ) ≤ 4*shifted ∧
    FSTwoLevel.rankError ≤ 1/(FSTwoLevel.fieldSize : ℚ)^2 ∧
    1 ≤ line 2894 := by
  simp only [line, slope, f, price, shifted, rate, baseline, capacity,
    FSStoppedSpectrum.theta, FSTwoLevel.fieldSize, FSTwoLevel.rankError,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem affine_majorant (a : ℕ) (ha : 2714 ≤ a) : f a ≤ line a := by
  by_cases hsmall : a < 2894
  · have hm : a ∈ List.range' 2714 180 := by
      simp only [List.mem_range']
      exact ⟨a-2714, by omega, by omega⟩
    exact of_decide_eq_true ((List.all_eq_true.mp checked_ranges) a hm)
  · have hcast : (2894 : ℚ) ≤ a := by exact_mod_cast (show 2894 ≤ a by omega)
    have hp : f a ≤ 1 := price_le_one _ _ checked.1 (by unfold capacity; positivity)
    have hm : line 2894 ≤ line a := by
      unfold line
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (sub_le_sub_right hcast _) checked.2.2.1)
    exact hp.trans (checked.2.2.2.2.2.2.2.2.trans hm)

theorem capacity_le_one (a : ℕ) (ha : a ≤ 8192) : capacity a ≤ 1 := by
  unfold capacity
  apply (div_le_one (by exact_mod_cast Nat.choose_pos (show 81 ≤ 8192 by decide))).mpr
  exact_mod_cast Nat.choose_le_choose 81 ha

theorem f_le_one_sub_shifted (a : ℕ) (ha : a ≤ 8192) : f a ≤ 1-shifted := by
  have hp := price_mono shifted (capacity a) 1 checked.1
    (by unfold capacity; positivity) (capacity_le_one a ha)
  have he : price shifted 1 = 1-shifted := by
    simp only [price, if_neg (not_le.mpr checked.2.1), div_one]
  exact hp.trans_eq he

end RecursivePolygero.Instances.FSDefectData
