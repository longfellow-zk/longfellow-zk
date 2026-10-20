import polygero.Instances.FSBaselineAwareData

/-! A barrier for the SUPPORT-ONLY capacity relaxation. This module does
not construct a Polygero commitment or an accepting adversary. -/
namespace RecursivePolygero.Instances.FSStoppingAudit
open Bcs.StoppedPotential

/-- Four equiprobable reusable states force this rate in a static Bellman
certificate. This is a premise barrier, not a success-probability attack. -/
theorem four_state_rate_lower_bound (q capacity rate : ℚ) (hq : 0 < q)
    (hc : 0 < capacity) (hroot : 4*repeatPrice rate capacity/q ≤ rate) :
    4*capacity/(q*capacity+4) ≤ rate := by
  have hl : 1-rate/capacity ≤ repeatPrice rate capacity := by
    simp only [repeatPrice,if_neg hc.ne']
    exact le_max_right _ _
  have ht := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num)) hq.le).trans hroot
  have hm := mul_le_mul_of_nonneg_right ht (mul_pos hq hc).le
  have he : (4*(1-rate/capacity)/q)*(q*capacity) = 4*capacity-4*rate := by field_simp
  rw [he] at hm
  apply (div_le_iff₀ (by positivity : 0 < q*capacity+4)).mpr
  nlinarith

def capacity : ℚ := FSBaselineAwareData.baseline+FSBaselineAwareData.capacity 2975
def barrier : ℚ := 4*capacity/(FSTwoLevel.fieldSize*capacity+4)

/-- The explicit support-only relaxation needs more than 3.95 field units,
even though its exact baseline-aware upper certificate uses only 3.97. -/
theorem checked : (395/100 : ℚ)/FSTwoLevel.fieldSize < barrier ∧
    FSDefect81.sameIOPError < barrier := by
  simp only [barrier,capacity,FSBaselineAwareData.baseline,FSBaselineAwareData.capacity,
    FSDefectData.baseline,FSDefectData.capacity,FSStoppedSpectrum.theta,FSTwoLevel.fieldSize,
    FSDefect81.sameIOPError,FiatShamir.twoError,ProfileAnalysis.profile,FSTwoLevel.theta,
    FSDefect81.parent,FSWholeBlock81.parent,FSBaselinePrice.row,FSDefect81.childRow,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,
    Nat.choose_eq_fast_choose]
  decide +kernel

end RecursivePolygero.Instances.FSStoppingAudit
