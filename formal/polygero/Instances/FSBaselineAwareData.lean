import polygero.Instances.FSDefect81
import polygero.Local.BaselineAwarePrice

/-! Rational certificates for baseline-aware stopping at 81/80 openings.
The four-system case now spends the total core size instead of bounding
each individual price by one. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace RecursivePolygero.Instances.FSBaselineAwareData
open ProfileAnalysis.StoppedSpectrum

def rate : ℚ := (397/100 : ℚ)/FSTwoLevel.fieldSize
def effective : ℚ := (333/100 : ℚ)/FSTwoLevel.fieldSize
def baseline : ℚ := FSDefectData.baseline
def bound : ℚ := 3969/1000
def capacity (a : ℕ) : ℚ := FSDefectData.capacity a
noncomputable def f (a : ℕ) : ℚ := price effective (capacity a)
noncomputable def slope : ℚ := (f 2866-f 2714)/152
noncomputable def slope4 : ℚ := f 2977-f 2976
noncomputable def line (a : ℕ) : ℚ := f 2714+slope*((a : ℚ)-2714)
noncomputable def line4 (a : ℕ) : ℚ := f 2976+slope4*((a : ℚ)-2976)
noncomputable def rangeValid (count : ℕ) (line : ℕ → ℚ) : Bool :=
  (List.range' 2714 count).all (fun a => decide (f a ≤ line a))

theorem checked_ranges : rangeValid 206 line = true ∧ rangeValid 301 line4 = true := by
  simp only [rangeValid,line,line4,slope,slope4,f,price,effective,capacity,
    FSDefectData.capacity,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

structure Numeric : Prop where
  effective_pos : 0 < effective
  rate_nonneg : 0 ≤ rate
  discriminant : (baseline+4*effective)^2 ≤ 16*effective*rate
  branch : baseline+2*effective ≤ 2*rate
  slope_nonneg : 0 ≤ slope
  slope4_nonneg : 0 ≤ slope4
  three : (3 : ℚ) ≤ bound
  four : 4*f 2976 ≤ bound
  five : 5*f 2714+slope*(14272-5*2714) ≤ bound
  six : 6*f 2714+slope*(16992-6*2714) ≤ bound
  end_line : 1 ≤ line 2920
  end_line4 : 1 ≤ line4 3015
  remainder : FSTwoLevel.rankError+bound/FSTwoLevel.fieldSize+
    6/(FSTwoLevel.fieldSize : ℚ)^2 ≤ rate
  fresh : FSTwoLevel.rankError+baseline+
    (1-FSStoppedSpectrum.theta 81 2714+6*FSStoppedSpectrum.theta 81 2714)/FSTwoLevel.fieldSize ≤ rate
  child : FSDefect81.childPrice ≤ rate
  improvement : rate < FSDefect81.price
  iop_intercept : 2*rate+FSDefect81.childPrice ≤ 2*(1871/1000 : ℚ)*FSDefect81.sameIOPError
  iop_slope : rate ≤ (1871/1000 : ℚ)*FSDefect81.sameIOPError
  relaxation_barrier : (395/100 : ℚ)/FSTwoLevel.fieldSize <
    4*Bcs.StoppedPotential.repeatPrice ((395/100 : ℚ)/FSTwoLevel.fieldSize)
      (baseline+capacity 2975)/FSTwoLevel.fieldSize

theorem checked : Numeric := by
  constructor <;>
    simp only [rate,effective,baseline,bound,capacity,line,line4,slope,slope4,f,price,
      FSDefectData.baseline,FSDefectData.capacity,FSStoppedSpectrum.theta,FSTwoLevel.fieldSize,
      FSTwoLevel.rankError,FSDefect81.price,FSDefect81.childPrice,FSWholeBlock81.childPrice,
      FSDefect81.sameIOPError,FiatShamir.twoError,ProfileAnalysis.profile,FSTwoLevel.theta,
      FSDefect81.parent,FSWholeBlock81.parent,FSBaselinePrice.row,FSDefect81.childRow,
      FSWholeBlock81.childRow,FSIntegerAffine.childRow,Bcs.StoppedPotential.repeatPrice,
      Nat.choose_eq_fast_choose] <;>
    decide +kernel

theorem affine_majorant (a : ℕ) (ha : 2714 ≤ a) : f a ≤ line a := by
  by_cases hsmall : a < 2920
  · have hm : a ∈ List.range' 2714 206 := by
      simp only [List.mem_range']; exact ⟨a-2714,by omega,by omega⟩
    exact of_decide_eq_true ((List.all_eq_true.mp checked_ranges.1) a hm)
  · have hp : f a ≤ 1 := price_le_one _ _ checked.effective_pos (by unfold capacity FSDefectData.capacity; positivity)
    have hm : line 2920 ≤ line a := by
      unfold line
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ checked.slope_nonneg
      exact sub_le_sub_right (by exact_mod_cast (show 2920 ≤ a by omega)) _
    exact hp.trans (checked.end_line.trans hm)

theorem affine_majorant4 (a : ℕ) (ha : 2714 ≤ a) : f a ≤ line4 a := by
  by_cases hsmall : a < 3015
  · have hm : a ∈ List.range' 2714 301 := by
      simp only [List.mem_range']; exact ⟨a-2714,by omega,by omega⟩
    exact of_decide_eq_true ((List.all_eq_true.mp checked_ranges.2) a hm)
  · have hp : f a ≤ 1 := price_le_one _ _ checked.effective_pos (by unfold capacity FSDefectData.capacity; positivity)
    have hm : line4 3015 ≤ line4 a := by
      unfold line4
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ checked.slope4_nonneg
      exact sub_le_sub_right (by exact_mod_cast (show 3015 ≤ a by omega)) _
    exact hp.trans (checked.end_line4.trans hm)

end RecursivePolygero.Instances.FSBaselineAwareData
