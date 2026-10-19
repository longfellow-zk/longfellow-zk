import polygero.Benchmarks.FSTwoLevel
import Bcs.GrindingBounds

/-! Exact feasibility certificate for a three-cluster grinding construction.
The arithmetic here does not assert existence of an adversary. A concrete
realization must supply the polynomial tableaux, fresh parent commitments,
child witness encodings, and the indicated independent oracle samples. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace RecursivePolygero.Benchmarks.FSGrinding
open Bcs.GrindingBounds
open Finset
open scoped BigOperators

/-- A degree-511 common-root polynomial, three blocks of 2560 columns,
and one unused column fit exactly in the verified n=8192 geometry. -/
def commonColumns : ℕ := 511
def blockColumns : ℕ := 2560
def agreementColumns : ℕ := commonColumns + blockColumns

theorem column_accounting : commonColumns + 3 * blockColumns + 1 = 8192 ∧
    agreementColumns = 3071 ∧ commonColumns < 512 := by decide

def fieldSize : ℕ := 2^128
/-- Union of three distinct lines through zero in the two equation weights. -/
def rootHit : ℚ := 3 / (fieldSize : ℚ) - 2 / (fieldSize : ℚ)^2

def queryHit : ℚ := (Nat.choose agreementColumns 81 : ℚ) / Nat.choose 8192 81

def totalQueries : ℕ := 2^122
/-- Reserve enough distinct child commitments for four expected hits. -/
def childAttempts : ℕ :=
  (4 * Nat.choose 8192 81 + Nat.choose agreementColumns 81 - 1) /
    Nat.choose agreementColumns 81

def parentAttempts : ℕ := totalQueries - childAttempts - 2
/-- Bonferroni lower bound for independent fresh parent samples. -/
def rootLower : ℚ := parentAttempts * rootHit - (Nat.choose parentAttempts 2 : ℚ) * rootHit^2
/-- A small binomial prefix bounds the reciprocal failure probability,
without constructing an enormous rational power. -/
def childPrefix : ℚ := ∑ j ∈ range 9, (Nat.choose childAttempts j : ℚ) * queryHit^j

def childLower : ℚ := 1 - 1 / childPrefix
/-- One varied child column is ignored by a uniform 80-column terminal query. -/
def terminalSuccess : ℚ := (8192 - 80 : ℕ) / (8192 : ℚ)

def candidateLower : ℚ := rootLower * childLower * terminalSuccess

def referenceError : ℚ :=
  let a := FSTwoLevel.theta (FSTwoLevel.data .threeBit)
  let b := FSTwoLevel.theta (FSTwoLevel.childData .threeBit)
  let e₀ := a + (1-a) * (FSTwoLevel.rankError + 1 / (fieldSize : ℚ))
  let e₁ := b + (1-b) * (FSTwoLevel.rankError + 1 / (fieldSize : ℚ))
  e₀ + (1-e₀) * e₁

def noLossUpper : ℚ := (totalQueries + 1 : ℕ) * referenceError

def renewalRate : ℚ := rootHit * queryHit / (rootHit + queryHit)

/-- These are numerical conditions for an obstruction, not a Polygero
attack theorem. Every comparison uses exact rational kernel computation. -/
theorem checked :
    childAttempts + parentAttempts + 2 = totalQueries ∧
    8 ≤ childAttempts ∧ 0 < queryHit ∧ queryHit < 1 ∧
    4 ≤ (childAttempts : ℚ) * queryHit ∧
    0 < rootLower ∧ 0 < childLower ∧
    (423 : ℚ) / 10000 < candidateLower ∧
    noLossUpper < (413 : ℚ) / 10000 ∧
    referenceError < renewalRate := by
  simp only [childAttempts, parentAttempts, totalQueries, rootLower, childLower,
    childPrefix, queryHit, agreementColumns, commonColumns, blockColumns, rootHit,
    fieldSize, candidateLower, terminalSuccess, noLossUpper, referenceError,
    renewalRate, FSTwoLevel.theta, FSTwoLevel.data, FSTwoLevel.childData,
    FSTwoLevel.rankError, FSTwoLevel.fieldSize, Nat.choose_eq_fast_choose,
    sum_range_succ, sum_range_zero, zero_add]
  decide +kernel

/-- The original verified 70-opening row uses cutoff 2109 at both levels.
The constants are repeated here to keep this arithmetic audit independent
of the original table's native numerical proof. -/
def originalQueryHit : ℚ := (Nat.choose agreementColumns 70 : ℚ) / Nat.choose 8192 70

def originalTotal : ℕ := 2^114

def originalChildAttempts : ℕ :=
  (4 * Nat.choose 8192 70 + Nat.choose agreementColumns 70 - 1) /
    Nat.choose agreementColumns 70

def originalParentAttempts : ℕ := originalTotal - originalChildAttempts - 2

def originalChildPrefix : ℚ := ∑ j ∈ range 9,
  (Nat.choose originalChildAttempts j : ℚ) * originalQueryHit^j

def originalLower : ℚ :=
  (originalParentAttempts * rootHit - (Nat.choose originalParentAttempts 2 : ℚ) * rootHit^2) *
    (1 - 1 / originalChildPrefix) * ((8192 - 70 : ℕ) / (8192 : ℚ))

def originalReferenceError : ℚ :=
  let theta := (Nat.choose 2108 70 : ℚ) / Nat.choose 8192 70
  let e := theta + (1-theta) * (FSTwoLevel.rankError + 1 / (fieldSize : ℚ))
  e + (1-e) * e

def originalNoLossUpper : ℚ := (originalTotal + 1 : ℕ) * originalReferenceError

theorem original70_checked :
    originalChildAttempts + originalParentAttempts + 2 = originalTotal ∧
    8 ≤ originalChildAttempts ∧ 0 < originalQueryHit ∧ originalQueryHit < 1 ∧
    4 ≤ (originalChildAttempts : ℚ) * originalQueryHit ∧
    (17 : ℚ) / 100000 < originalLower ∧
    originalNoLossUpper < (123 : ℚ) / 1000000 ∧
    originalNoLossUpper * (7 / 5 : ℚ) < originalLower := by
  simp only [originalChildAttempts, originalParentAttempts, originalTotal,
    originalQueryHit, originalChildPrefix, originalLower, rootHit, fieldSize,
    agreementColumns, commonColumns, blockColumns, originalNoLossUpper,
    originalReferenceError, FSTwoLevel.rankError, FSTwoLevel.fieldSize,
    Nat.choose_eq_fast_choose, sum_range_succ, sum_range_zero, zero_add]
  decide +kernel

end RecursivePolygero.Benchmarks.FSGrinding
