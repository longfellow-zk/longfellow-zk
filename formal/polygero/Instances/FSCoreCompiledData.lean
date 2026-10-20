import polygero.Instances.FSCoreData
import polygero.Instances.FSCompiledData
namespace RecursivePolygero.Instances.FSCoreCompiledData
open FSCompiledData
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-- Budget-aware comparison: a positive Merkle budget pays the child
intercept. Zero-Merkle executions are handled by root guessing instead. -/
theorem checked :
    FSCoreData.rate+reserve ≤ (191/100 : ℚ)*FSIOPReference81.strongIOPError ∧
    FSCoreData.rate+reserve ≤ (1353/1000 : ℚ)*FSDefect81.sameIOPError ∧
    FSDefect81.childPrice+1/(FSTwoLevel.fieldSize : ℚ) ≤ FSCoreData.rate ∧
    reserve ≤ (191/100 : ℚ)*FSIOPReference81.strongIOPError ∧
    reserve ≤ (1353/1000 : ℚ)*FSDefect81.sameIOPError := by
  simp only [reserve,digestSize,checking,FSCoreData.rate,
    FSDefect81.childPrice,FSWholeBlock81.childPrice,FSDefect81.sameIOPError,
    FSIOPReference81.strongIOPError,FSIOPReference81.localError,FSIOPReference81.threshold,
    FSIOPReference81.ratio,DiscreteThreshold.candidate,FiatShamir.twoError,ProfileAnalysis.profile,FSTwoLevel.theta,
    FSDefect81.parent,FSWholeBlock81.parent,FSBaselinePrice.row,FSDefect81.childRow,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,FSTwoLevel.fieldSize,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem comparison (t n : ℕ) (ht : t ≤ fuelCap) (hn : n ≤ fuelCap) (hpos : 1 ≤ t)
    (K e : ℚ) (hs : FSCoreData.rate+reserve ≤ K*e) :
    FSCoreData.rate+FSDefect81.childPrice+n*FSCoreData.rate+bcs t n ≤ K*(n+t+1)*e := by
  have htq : (1 : ℚ) ≤ t := by exact_mod_cast hpos
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  have hr := FSCoreData.checked.rate_nonneg
  have hz : (0 : ℚ) ≤ reserve := by unfold reserve; positivity
  have he := bcs_le_budget t n ht hn
  have he' : bcs t n ≤ (t : ℚ)*(1/(FSTwoLevel.fieldSize : ℚ))+(n+1)*reserve := by
    simpa only [div_eq_mul_inv,one_mul] using he
  have hp := checked.2.2.1
  have hh : FSDefect81.childPrice ≤ (t : ℚ)*(FSCoreData.rate-1/(FSTwoLevel.fieldSize : ℚ)) := by
    have hc := FSCompletion81.checked.2.2.2.2
    nlinarith [mul_nonneg (sub_nonneg.mpr htq) (show 0 ≤ FSCoreData.rate-1/(FSTwoLevel.fieldSize : ℚ) by linarith)]
  have hk : 0 ≤ K*e := (add_nonneg hr hz).trans hs
  nlinarith [he',mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ (n : ℚ)+t+1 by positivity),
    mul_nonneg (show (0 : ℚ) ≤ t by positivity) hz]

end RecursivePolygero.Instances.FSCoreCompiledData
