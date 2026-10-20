import polygero.Instances.FSShiftedData
import polygero.Instances.FSCompiledData
import polygero.Instances.FSCoreStoppingAudit
namespace RecursivePolygero.Instances.FSShiftedCompiledData
open FSCompiledData
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
/-- Budget-aware comparison: a positive Merkle budget pays the child
intercept. Zero-Merkle executions are handled by root guessing instead. -/
theorem checked :
    FSShiftedData.rate+reserve ≤ (3781/2000 : ℚ)*FSIOPReference81.strongIOPError ∧
    FSShiftedData.rate+reserve ≤ (1339/1000 : ℚ)*FSDefect81.sameIOPError ∧
    FSDefect81.childPrice+1/(FSTwoLevel.fieldSize : ℚ) ≤ FSShiftedData.rate ∧
    reserve ≤ (3781/2000 : ℚ)*FSIOPReference81.strongIOPError ∧
    reserve ≤ (1339/1000 : ℚ)*FSDefect81.sameIOPError := by
  simp only [reserve,digestSize,checking,FSShiftedData.rate,
    FSDefect81.childPrice,FSWholeBlock81.childPrice,FSDefect81.sameIOPError,
    FSIOPReference81.strongIOPError,FSIOPReference81.localError,FSIOPReference81.threshold,
    FSIOPReference81.ratio,DiscreteThreshold.candidate,FiatShamir.twoError,ProfileAnalysis.profile,FSTwoLevel.theta,
    FSDefect81.parent,FSWholeBlock81.parent,FSBaselinePrice.row,FSDefect81.childRow,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,FSTwoLevel.fieldSize,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem comparison (t n : ℕ) (ht : t ≤ fuelCap) (hn : n ≤ fuelCap) (hpos : 1 ≤ t)
    (K e : ℚ) (hs : FSShiftedData.rate+reserve ≤ K*e) :
    FSShiftedData.rate+FSDefect81.childPrice+n*FSShiftedData.rate+bcs t n ≤ K*(n+t+1)*e := by
  have htq : (1 : ℚ) ≤ t := by exact_mod_cast hpos
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  have hr := FSShiftedData.checked.rate_nonneg
  have hz : (0 : ℚ) ≤ reserve := by unfold reserve; positivity
  have he := bcs_le_budget t n ht hn
  have he' : bcs t n ≤ (t : ℚ)*(1/(FSTwoLevel.fieldSize : ℚ))+(n+1)*reserve := by
    simpa only [div_eq_mul_inv,one_mul] using he
  have hp := checked.2.2.1
  have hh : FSDefect81.childPrice ≤ (t : ℚ)*(FSShiftedData.rate-1/(FSTwoLevel.fieldSize : ℚ)) := by
    have hc := FSCompletion81.checked.2.2.2.2
    nlinarith [mul_nonneg (sub_nonneg.mpr htq) (show 0 ≤ FSShiftedData.rate-1/(FSTwoLevel.fieldSize : ℚ) by linarith)]
  have hk : 0 ≤ K*e := (add_nonneg hr hz).trans hs
  nlinarith [he',mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ (n : ℚ)+t+1 by positivity),
    mul_nonneg (show (0 : ℚ) ≤ t by positivity) hz]

/-- The remaining scalar certificate slack is below 0.0001 field units.
This is a statement about the support relaxation, not attack optimality. -/
theorem static_gap :
    (37809/10000 : ℚ)/FSTwoLevel.fieldSize < FSCoreStoppingAudit.barrier ∧
    FSShiftedData.rate < FSCoreStoppingAudit.barrier+(1/10000 : ℚ)/FSTwoLevel.fieldSize := by
  simp only [FSShiftedData.rate,FSCoreStoppingAudit.barrier,FSCoreStoppingAudit.capacity,
    FSCoreData.baseline,FSCoreData.capacity,FSDefectData.baseline,FSDefectData.capacity,
    FSStoppedSpectrum.theta,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel
/-- Improving only the parent cannot remove every bit through the
current maximum-price composition: its unchanged child certificate is
already larger than the stronger complete IOP reference. This is a
certificate bottleneck, not a lower bound on actual acceptance. -/
theorem current_child_above_reference :
    FSIOPReference81.strongIOPError < FSDefect81.childPrice := by
  simp only [FSDefect81.childPrice,FSWholeBlock81.childPrice,
    FSIOPReference81.strongIOPError,FSIOPReference81.localError,FSIOPReference81.threshold,
    FSIOPReference81.ratio,DiscreteThreshold.candidate,FiatShamir.twoError,ProfileAnalysis.profile,
    FSTwoLevel.theta,FSDefect81.childRow,FSWholeBlock81.childRow,FSIntegerAffine.childRow,
    FSTwoLevel.rankError,FSTwoLevel.fieldSize,Nat.choose_eq_fast_choose]
  decide +kernel

theorem current_max_slope_obstruction (parent : ℚ) :
    FSIOPReference81.strongIOPError < max parent FSDefect81.childPrice :=
  current_child_above_reference.trans_le (le_max_right _ _)

end RecursivePolygero.Instances.FSShiftedCompiledData
