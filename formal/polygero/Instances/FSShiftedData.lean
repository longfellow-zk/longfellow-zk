import polygero.Instances.FSCoreData
import polygero.Local.ShiftedEnvelope
import polygero.Local.BaselineAwarePrice

/-! Rational certificates for actual-core stopping at unchanged 81/80 openings.
Outside-core exceptions have already paid their second field constraint. -/
set_option maxRecDepth 50000
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

namespace RecursivePolygero.Instances.FSShiftedData
open ProfileAnalysis.ShiftedSpectrum

def rate : ℚ := (3781/1000 : ℚ)/FSTwoLevel.fieldSize
def pivot : ℚ := (5686/1000 : ℚ)/FSTwoLevel.fieldSize
def baseline : ℚ := FSDefectData.baseline
def bound : ℚ := 378095/100000
def capacity (a : ℕ) : ℚ := FSDefectData.capacity a
noncomputable def f (a : ℕ) : ℚ := price baseline pivot (capacity a)
noncomputable def slope : ℚ := (f 2878-f 2650)/228
noncomputable def slope4 : ℚ := f 2913-f 2912
noncomputable def line (a : ℕ) : ℚ := f 2650+slope*((a : ℚ)-2650)
noncomputable def line4 (a : ℕ) : ℚ := f 2912+slope4*((a : ℚ)-2912)
noncomputable def rangeValid (count : ℕ) (line : ℕ → ℚ) : Bool :=
  (List.range' 2650 count).all (fun a => decide (f a ≤ line a))

theorem checked_ranges : rangeValid 270 line = true ∧ rangeValid 350 line4 = true := by
  simp only [rangeValid,line,line4,slope,slope4,f,price,tangentRate,baseline,pivot,FSDefectData.baseline,FSStoppedSpectrum.theta,capacity,
    FSDefectData.capacity,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

structure Numeric : Prop where
  pivot_pos : 0 < pivot
  baseline_nonneg : 0 ≤ baseline
  rate_nonneg : 0 ≤ rate
  tangent : tangentRate baseline pivot ≤ rate
  slope_nonneg : 0 ≤ slope
  slope4_nonneg : 0 ≤ slope4
  three : (3 : ℚ) ≤ bound
  four : 4*f 2912 ≤ bound
  five : 5*f 2650+slope*(13952-5*2650) ≤ bound
  six : 6*f 2650+slope*(16608-6*2650) ≤ bound
  end_line : 1 ≤ line 2920
  end_line4 : 1 ≤ line4 3000
  remainder : FSTwoLevel.rankError+bound/FSTwoLevel.fieldSize+
    6*8192/(FSTwoLevel.fieldSize : ℚ)^2 ≤ rate
  fresh : FSTwoLevel.rankError+baseline+
    (1-FSStoppedSpectrum.theta 81 2714+6*FSStoppedSpectrum.theta 81 2714)/FSTwoLevel.fieldSize ≤ rate
  child : FSDefect81.childPrice ≤ rate
  improvement : rate < FSCoreData.rate

theorem checked : Numeric := by
  constructor <;>
    simp only [rate,pivot,baseline,bound,capacity,line,line4,slope,slope4,f,price,tangentRate,
      FSDefectData.baseline,FSDefectData.capacity,FSStoppedSpectrum.theta,FSTwoLevel.fieldSize,
      FSTwoLevel.rankError,FSCoreData.rate,FSDefect81.childPrice,FSWholeBlock81.childPrice,
      FSDefect81.sameIOPError,FiatShamir.twoError,ProfileAnalysis.profile,FSTwoLevel.theta,
      FSDefect81.parent,FSWholeBlock81.parent,FSBaselinePrice.row,FSDefect81.childRow,
      FSWholeBlock81.childRow,FSIntegerAffine.childRow,Nat.choose_eq_fast_choose] <;>
    decide +kernel

theorem affine_majorant (a : ℕ) (ha : 2650 ≤ a) : f a ≤ line a := by
  by_cases hsmall : a < 2920
  · have hm : a ∈ List.range' 2650 270 := by
      simp only [List.mem_range']; exact ⟨a-2650,by omega,by omega⟩
    exact of_decide_eq_true ((List.all_eq_true.mp checked_ranges.1) a hm)
  · have hp : f a ≤ 1 := price_le_one baseline pivot checked.baseline_nonneg checked.pivot_pos _ (by unfold capacity FSDefectData.capacity; positivity)
    have hm : line 2920 ≤ line a := by
      unfold line
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ checked.slope_nonneg
      exact sub_le_sub_right (by exact_mod_cast (show 2920 ≤ a by omega)) _
    exact hp.trans (checked.end_line.trans hm)

theorem affine_majorant4 (a : ℕ) (ha : 2650 ≤ a) : f a ≤ line4 a := by
  by_cases hsmall : a < 3000
  · have hm : a ∈ List.range' 2650 350 := by
      simp only [List.mem_range']; exact ⟨a-2650,by omega,by omega⟩
    exact of_decide_eq_true ((List.all_eq_true.mp checked_ranges.2) a hm)
  · have hp : f a ≤ 1 := price_le_one baseline pivot checked.baseline_nonneg checked.pivot_pos _ (by unfold capacity FSDefectData.capacity; positivity)
    have hm : line4 3000 ≤ line4 a := by
      unfold line4
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ checked.slope4_nonneg
      exact sub_le_sub_right (by exact_mod_cast (show 3000 ≤ a by omega)) _
    exact hp.trans (checked.end_line4.trans hm)

end RecursivePolygero.Instances.FSShiftedData
