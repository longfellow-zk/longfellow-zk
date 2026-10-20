import Bcs.FiniteRenewal
import polygero.Instances.FSCompiledData
import polygero.Instances.FSCoreStoppingAudit

/-! The four-core static obstruction is not itself a bounded-work attack.
Only the ordered fresh-sample renewal model is covered here. Actual ROM
queries may be cached or interleaved; that transport is a separate premise. -/
namespace RecursivePolygero.Instances.FSFiniteHorizon81
open Bcs.StoppedPotential

def rootRate : ℚ := 4/FSTwoLevel.fieldSize
def childRate : ℚ := FSCoreStoppingAudit.capacity

theorem checked : 0 ≤ rootRate ∧ rootRate ≤ 1 ∧ 0 ≤ childRate ∧ childRate ≤ 1 ∧
    (FSCompiledData.fuelCap : ℚ)*rootRate*childRate/2 ≤ (54/100 : ℚ)/FSTwoLevel.fieldSize := by
  simp only [rootRate,childRate,FSCoreStoppingAudit.capacity,FSCoreData.baseline,
    FSCoreData.capacity,FSDefectData.baseline,FSDefectData.capacity,FSStoppedSpectrum.theta,
    FSCompiledData.fuelCap,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

/-- At the actual work cap, the abstract four-state renewal family costs
less than 0.54 field units per work unit, despite its >3.78 stationary
Bellman barrier. This is not yet a bound on the actual Polygero ROM. -/
theorem ordered_four_core_bound (n : ℕ) (hn : n ≤ FSCompiledData.fuelCap) :
    renewalSearch rootRate childRate n ≤ (n : ℚ)*((54/100 : ℚ)/FSTwoLevel.fieldSize) := by
  obtain ⟨hr,hr1,hc,hc1,hb⟩ := checked
  exact renewalSearch_le_budget rootRate childRate FSTwoLevel.fieldSize FSCompiledData.fuelCap
    (54/100) hr hr1 hc hc1 (by norm_num [FSTwoLevel.fieldSize])
    (Nat.cast_nonneg _) hb n (Nat.cast_le.mpr hn)
/-- Even allowing an immediate child trial at every root creation, the
bounded scalar obstruction costs at most 0.54/q in the (n+1) convention. -/
theorem immediate_four_core_bound (n : ℕ) (hn : n ≤ FSCompiledData.fuelCap) :
    renewalImmediate rootRate childRate n ≤ (n+1)*((54/100 : ℚ)/FSTwoLevel.fieldSize) := by
  obtain ⟨hr,hr1,hc,hc1,hb⟩ := checked
  exact renewalImmediate_le_budget rootRate childRate FSTwoLevel.fieldSize FSCompiledData.fuelCap
    (54/100) hr hr1 hc hc1 (by norm_num [FSTwoLevel.fieldSize])
    (Nat.cast_nonneg _) hb n (Nat.cast_le.mpr hn)
theorem baseline_checked :
    FSCoreData.baseline+(54/100 : ℚ)/FSTwoLevel.fieldSize ≤ (1752/1000 : ℚ)/FSTwoLevel.fieldSize := by
  simp only [FSCoreData.baseline,FSDefectData.baseline,FSStoppedSpectrum.theta,
    FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

/-- The stationary four-core obstruction is bypassed in this finite
renewal calculation even after retaining the full uniform baseline. The
actual ROM reduction and other system families are not asserted here. -/
theorem baseline_immediate_four_core_bound (n : ℕ) (hn : n ≤ FSCompiledData.fuelCap) :
    (n : ℚ)*FSCoreData.baseline+renewalImmediate rootRate childRate n ≤
      (n+1)*((1752/1000 : ℚ)/FSTwoLevel.fieldSize) := by
  have hi := immediate_four_core_bound n hn
  have hb := mul_le_mul_of_nonneg_left baseline_checked (show 0 ≤ (n : ℚ)+1 by positivity)
  have hbase : 0 ≤ FSCoreData.baseline := by
    unfold FSCoreData.baseline FSDefectData.baseline FSStoppedSpectrum.theta
    exact mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  nlinarith

end RecursivePolygero.Instances.FSFiniteHorizon81
