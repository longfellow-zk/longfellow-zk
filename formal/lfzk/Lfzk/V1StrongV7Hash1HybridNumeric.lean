import Lfzk.GradedCoreGrid
import Lfzk.V1StrongV7Numeric

/-! Exact arithmetic for the v7 hash1 hybrid FS bound.  The direct V1
terminal density is bounded by its existing checked six-count certificate;
the hash-side field term remains in both the constant and query budgets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Hash1HybridNumeric

open Lfzk.CertifiedV1 Lfzk.NizkZk

def sigChallenge : ℚ :=
  v7SigHahn.params.row.fail + v7SigHahn.params.row.arith

def sigQuery : ℚ := v7SigHahn.params.row.cover

/-- An alphabet-independent upper bound on the exact hybrid slot sum,
including the direct V1 terminal event once. -/
def coreUpper : ℚ :=
  (4 : ℚ) / 2 ^ 128 +
    (v7Hash1.cardCand : ℚ) * zkFieldDensity v7Hash1 3 +
    (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
    sigChallenge + sigQuery + (6 : ℚ) / 2 ^ 128

/-- An alphabet-independent upper bound per adaptive oracle query. -/
def queryUpper : ℚ :=
  max (max (v7Hash1.zkCoefficient 3)
    (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) +
    (6 : ℚ) / 2 ^ 128

/-- The exact role-based budget at the modeled 256-bit combined challenge
alphabet, with its balanced 128-bit MAC-key decoder. -/
def hybridBudget (N : ℕ) : ℚ :=
  Lfzk.NizkZkDeployedHash.gradedCombinedBudget
    v7Hash1 v7SigHahn 3 8 (2 ^ 256) N
    (4 * 2 ^ 128 : ℚ) 0 0 sigChallenge sigQuery +
    (N + 1 : ℕ) * Lfzk.V1StrongV7Numeric.density 0

/-- The concrete compiler maximum and slot sum are exactly the budget used
by the checked numerical certificate.  This is the arithmetic connection
between the merged FS schedule and the v7 hash1 certificate. -/
theorem hybridBudget_eq_role (N : ℕ) :
    ((N : ℚ) * Lfzk.NizkZkDeployedHash.twoFieldPotentialMaxBudget
        v7Hash1 v7SigHahn 3 8 (2 ^ 256)
        (4 * 2 ^ 128 : ℚ) 0 0
        ((2 ^ 256 : ℚ) * sigChallenge)
        ((2 ^ 256 : ℚ) * sigQuery) +
      Lfzk.NizkZkDeployedHash.twoFieldPotentialTotalBudget
        v7Hash1 v7SigHahn 3 8 (2 ^ 256)
        (4 * 2 ^ 128 : ℚ) 0 0
        ((2 ^ 256 : ℚ) * sigChallenge)
        ((2 ^ 256 : ℚ) * sigQuery)) / (2 ^ 256 : ℚ) +
      (N + 1 : ℕ) * Lfzk.V1StrongV7Numeric.density 0 =
      hybridBudget N := by
  have hc : 0 ≤ (2 ^ 256 : ℚ) * sigChallenge := by
    native_decide
  have hq : 0 ≤ (2 ^ 256 : ℚ) * sigQuery := by
    native_decide
  simp only [hybridBudget, Lfzk.NizkZkDeployedHash.gradedCombinedBudget,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [max_eq_right hc, max_eq_right hq]
  simp

theorem hybridBudget_le_linear (N : ℕ) :
    hybridBudget N ≤ coreUpper + N * queryUpper := by
  have hs := Lfzk.GradedCoreGrid.v7GradedCosts_le_coefficient (0 : Fin 4)
  have hsigC : sigChallenge ≤ v7SigHahn.zkCoefficient 8 := by
    simpa only [sigChallenge] using hs.2.2.1
  have hsigQ : sigQuery ≤ v7SigHahn.zkCoefficient 8 := by
    simpa only [sigQuery] using hs.2.2.2
  have hgrid := Lfzk.NizkZkDeployedHash.gradedCombinedBudget_le_density
    v7Hash1 v7SigHahn 3 8 (2 ^ 256) (2 ^ 128) 2 2
    (2 ^ 128) N (by positivity) (by positivity)
    (by native_decide) (by native_decide)
    (by norm_num [← pow_add])
    0 0 sigChallenge sigQuery
    (by norm_num) (by norm_num)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) hsigC hsigQ
  have hgrid' :
      Lfzk.NizkZkDeployedHash.gradedCombinedBudget
        v7Hash1 v7SigHahn 3 8 (2 ^ 256) N
        (4 * 2 ^ 128 : ℚ) 0 0 sigChallenge sigQuery ≤
      (4 : ℚ) / 2 ^ 128 +
        (v7Hash1.cardCand : ℚ) * zkFieldDensity v7Hash1 3 +
        (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
        sigChallenge + sigQuery +
        N * max (max (v7Hash1.zkCoefficient 3)
          (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) := by
    convert hgrid using 1 <;> norm_num [sigChallenge, sigQuery]
  have hd := Lfzk.V1StrongV7Numeric.density_lt_six (0 : Fin 4)
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  have hdN : (N + 1 : ℕ) * Lfzk.V1StrongV7Numeric.density 0 ≤
      (N + 1 : ℕ) * ((6 : ℚ) / 2 ^ 128) := by
    exact mul_le_mul_of_nonneg_left hd.le (by positivity)
  dsimp only [hybridBudget, coreUpper, queryUpper,
    sigChallenge, sigQuery] at *
  simp only [Nat.cast_add, Nat.cast_one] at *
  nlinarith [hgrid']

def fc : ℕ :=
  2 * v7Hash1.params.row.n + 2 * v7SigHahn.params.row.n

def L : ℕ :=
  Lfzk.NizkAdaptiveTwoField.len2 v7Hash1 v7SigHahn

/-- The constant, adaptive-query, and commitment-query coefficients all
fit the 116-bit T-security envelope.  This does not assert 117 bits. -/
theorem linearSlack :
    coreUpper + 2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 116 ∧
    queryUpper + 2 * ((fc + 2 ^ 116 : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 116 ∧
    2 * ((3 * 2 ^ 116 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- The exact adaptive-Merkle numerator is bounded for every query count,
provided the commitment-hash budget is within the 116-bit T-security range. -/
theorem rhs_le_116 (N tA : ℕ) (htA : tA ≤ 2 ^ 116) :
    coreUpper + N * queryUpper +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
  obtain ⟨hc, hq, ht⟩ := linearSlack
  have hn := Lfzk.TSec.adaptiveNumerator_le_linear
    (fc := fc) (L := L) (N := N) (G := 2 ^ 116) htA
  have hm :
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤
      2 * ((fc * (1 + L) + N * (fc + 2 ^ 116) +
        tA * (3 * 2 ^ 116 + 2 * fc + 1 + L) : ℕ) : ℚ) /
        2 ^ 256 := by
    gcongr
  calc
    coreUpper + N * queryUpper +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
          2 ^ 256 ≤
      (coreUpper + 2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256) +
        N * (queryUpper + 2 * ((fc + 2 ^ 116 : ℕ) : ℚ) / 2 ^ 256) +
        tA * (2 * ((3 * 2 ^ 116 + 2 * fc + 1 + L : ℕ) : ℚ) /
          2 ^ 256) := by
            push_cast at hm ⊢
            nlinarith
    _ ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
      have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
      have htAq : (0 : ℚ) ≤ tA := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hq hN,
        mul_le_mul_of_nonneg_left ht htAq]

/-- The exact role-based hybrid budget, direct terminal count, and adaptive
Merkle term jointly satisfy 116-bit T-security for v7 hash1. -/
theorem hybridBudget_rhs_le_116 (N tA : ℕ) (htA : tA ≤ 2 ^ 116) :
    hybridBudget N +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
  have hb := hybridBudget_le_linear N
  have hr := rhs_le_116 N tA htA
  linarith

end Lfzk.V1StrongV7Hash1HybridNumeric
