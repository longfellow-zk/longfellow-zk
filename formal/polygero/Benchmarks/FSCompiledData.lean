import polygero.Benchmarks.FSBaselineAware81
import Bcs.AdaptiveCommit

/-! Exact 81/80 end-to-end arithmetic, including both Merkle errors. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace RecursivePolygero.Benchmarks.FSCompiledData
open Bcs.AdaptiveCommit FiatShamir FiatShamir.TwoLevel ProfileAnalysis

def digestSize : ℕ := 2^256
def fuelCap : ℕ := 2^120
def checking : ℕ := 32768
def bcs (t n : ℕ) : ℚ :=
  ((adaptiveNumerator checking t (n+4)+adaptiveNumerator checking t (n+3) : ℕ) : ℚ)/digestSize

def reserve : ℚ := (9*checking : ℕ)/(digestSize : ℚ)

theorem numerator_upper (t n : ℕ) :
    adaptiveNumerator checking t (n+4)+adaptiveNumerator checking t (n+3) ≤
      2*t^2+(checking+t)*(4*t+2*n+9) := by
  have hb : t*(t-1)/2 ≤ t^2 := (Nat.div_le_self _ _).trans (by
    have h := Nat.mul_le_mul_left t (Nat.sub_le t 1)
    simpa [pow_two] using h)
  unfold adaptiveNumerator
  nlinarith

/-- Merkle work pays the birthday and adaptive cross terms. The tiny
remaining FS-query/constant reserve is retained exactly, not dropped. -/
theorem bcs_le_budget (t n : ℕ) (ht : t ≤ fuelCap) (hn : n ≤ fuelCap) :
    bcs t n ≤ (t : ℚ)/FSTwoLevel.fieldSize+(n+1)*reserve := by
  have hu := Nat.cast_le (α := ℚ).mpr (numerator_upper t n)
  push_cast at hu
  have htq : (t : ℚ) ≤ fuelCap := by exact_mod_cast ht
  have hnq : (n : ℚ) ≤ fuelCap := by exact_mod_cast hn
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg _
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  have hcoef : (8*fuelCap+4*checking+9 : ℚ) ≤ FSTwoLevel.fieldSize := by
    norm_num [fuelCap,checking,FSTwoLevel.fieldSize]
  have hc : (2*checking : ℚ) ≤ 9*checking := by norm_num [checking]
  have hbound : ((adaptiveNumerator checking t (n+4)+adaptiveNumerator checking t (n+3) : ℕ) : ℚ) ≤
      (FSTwoLevel.fieldSize : ℚ)*t+(9*checking : ℚ)*(n+1) := by
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr htq) ht0,
      mul_nonneg (sub_nonneg.mpr hnq) ht0,
      mul_nonneg (sub_nonneg.mpr hcoef) ht0,
      mul_nonneg (sub_nonneg.mpr hc) hn0]
  unfold bcs reserve
  have hd : (0 : ℚ) < digestSize := by norm_num [digestSize]
  apply (div_le_iff₀ hd).mpr
  have he : ((t : ℚ)/FSTwoLevel.fieldSize+(n+1)*((9*checking : ℕ)/(digestSize : ℚ))) * digestSize =
      (FSTwoLevel.fieldSize : ℚ)*t+(9*checking : ℚ)*(n+1) := by
    norm_num [digestSize,FSTwoLevel.fieldSize]
    ring
  rw [he]
  exact hbound

/-- All decimals in the headline are rounded upwards and kernel checked. -/
theorem checked :
    2*FSBaselineAware81.price+FSDefect81.childPrice+2*reserve ≤
      2*(2641/1000 : ℚ)*FSIOPReference81.strongIOPError ∧
    FSBaselineAware81.price+reserve ≤ (2641/1000 : ℚ)*FSIOPReference81.strongIOPError ∧
    2*FSBaselineAware81.price+FSDefect81.childPrice+2*reserve ≤
      2*(1871/1000 : ℚ)*FSDefect81.sameIOPError ∧
    FSBaselineAware81.price+reserve ≤ (1871/1000 : ℚ)*FSDefect81.sameIOPError ∧
    1/(FSTwoLevel.fieldSize : ℚ) ≤ FSBaselineAware81.price+reserve ∧
    FSBaselineAware81.price+FSDefect81.childPrice+reserve ≤ 8/(FSTwoLevel.fieldSize : ℚ) ∧
    FSBaselineAware81.price+reserve ≤ 4/(FSTwoLevel.fieldSize : ℚ) ∧
    reserve ≤ (2641/1000 : ℚ)*FSIOPReference81.strongIOPError ∧
    reserve ≤ (1871/1000 : ℚ)*FSDefect81.sameIOPError := by
  simp only [reserve,digestSize,checking,FSBaselineAware81.price,FSBaselineAwareData.rate,
    FSDefect81.childPrice,FSWholeBlock81.childPrice,FSDefect81.sameIOPError,
    FSIOPReference81.strongIOPError,FSIOPReference81.localError,FSIOPReference81.threshold,
    FSIOPReference81.ratio,DiscreteThreshold.candidate,twoError,profile,FSTwoLevel.theta,
    FSDefect81.parent,FSWholeBlock81.parent,FSBaselinePrice.row,FSDefect81.childRow,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,FSTwoLevel.fieldSize,
    Nat.choose_eq_fast_choose]
  decide +kernel

/-- A comparison in total work, valid for every positive work budget. -/
theorem comparison (t n : ℕ) (ht : t ≤ fuelCap) (hn : n ≤ fuelCap) (hpos : 1 ≤ n+t)
    (K e : ℚ)
    (hi : 2*FSBaselineAware81.price+FSDefect81.childPrice+2*reserve ≤ 2*K*e)
    (hs : FSBaselineAware81.price+reserve ≤ K*e) :
    FSBaselineAware81.price+FSDefect81.childPrice+n*FSBaselineAware81.price+bcs t n ≤ K*(n+t+1)*e := by
  have hsum : (1 : ℚ) ≤ n+t := by exact_mod_cast hpos
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg _
  have he := bcs_le_budget t n ht hn
  have hp := checked.2.2.2.2.1
  have he' : bcs t n ≤ (t : ℚ)*(1/(FSTwoLevel.fieldSize : ℚ))+(n+1)*reserve := by
    simpa only [div_eq_mul_inv,one_mul] using he
  nlinarith [he',mul_nonneg ht0 (sub_nonneg.mpr hp),
    mul_nonneg (sub_nonneg.mpr hsum) (sub_nonneg.mpr hs)]

end RecursivePolygero.Benchmarks.FSCompiledData
