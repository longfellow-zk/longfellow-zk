import Lfzk.V1StrongV7Rows
import Lfzk.V1StrongHahnExtras
import LigeroFamily.Soundness.PolicyPotential
import LigeroFamily.Soundness.Hypergeometric

/-! Exact graded high-response arithmetic for the stronger v7 V1 rows. -/

set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Numeric

open LigeroFamily Lfzk.LigeroV1Rows

def row (i : Fin 4) : Row :=
  match i.val with
  | 0 => Lfzk.V1StrongV7Rows.hash1
  | 1 => Lfzk.V1StrongV7Rows.hash2
  | 2 => Lfzk.V1StrongV7Rows.hash3
  | _ => Lfzk.V1StrongV7Rows.hash4

def responseEndpoint (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 400966108258685
  | 1 => 296750042811368
  | 2 => 385824707325065
  | _ => 308529467083846

def responseSecondRadius (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 1700
  | 1 => 1744
  | 2 => 1764
  | _ => 1805

def responseSecondEndpoint (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 28849652485
  | 1 => 198458899828
  | 2 => 31273126198
  | _ => 220138078851

def responsePacking (i : Fin 4) (a : ℕ) : ℕ :=
  let R := row i
  let lambda := 2 * R.k - 2
  let endpoint := if i = 3 ∧ 1809 ≤ a then 21488178000
    else if responseSecondRadius i ≤ a then
      responseSecondEndpoint i
    else if i = 3 ∧ 1801 ≤ a then 10885581438852
    else responseEndpoint i
  if R.n * lambda < a * a then
    min endpoint (uncheckedAgreementListBound R.n lambda a)
  else endpoint

def cover (R : Row) (a : ℕ) : ℚ :=
  hypergeometricRatio a R.n R.openings

def cutoff (R : Row) : ℕ := R.n - R.e - 1

def highCurve (i : Fin 4) :
    PotentialProfile.Curve (row i).n where
  value a := if a ≤ cutoff (row i) then 0 else cover (row i) a
  zero := by simp [cutoff]
  nonneg := by
    intro a ha
    split_ifs
    · exact le_refl _
    · unfold cover hypergeometricRatio
      exact div_nonneg (by positivity) (by positivity)
  le_one := by
    intro a ha
    split_ifs
    · norm_num
    · unfold cover hypergeometricRatio
      have hquery : (row i).openings ≤ (row i).n := by
        fin_cases i <;> native_decide
      apply (div_le_one (by exact_mod_cast Nat.choose_pos hquery)).mpr
      exact_mod_cast Nat.choose_le_choose _ ha
  mono := by
    intro a b hab hbn
    by_cases hac : a ≤ cutoff (row i)
    · by_cases hbc : b ≤ cutoff (row i)
      · simp [hac, hbc]
      · simp only [hac, hbc, ↓reduceIte]
        unfold cover hypergeometricRatio
        exact div_nonneg (by positivity) (by positivity)
    · have hbc : ¬ b ≤ cutoff (row i) := by omega
      simp only [hac, hbc, ↓reduceIte]
      unfold cover hypergeometricRatio
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.choose_le_choose _ hab) (by positivity)

def tail (R : Row) (a : ℕ) : ℚ :=
  PolicyDoublyProfiledSoundnessClassifier.gradedTail
    (R.failureProfileAt R.fieldSize) R.arithProfile
    (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
      R.fieldSize R.g) R.fieldSize R.e R.g a

def highMass (i : Fin 4) : ℚ :=
  let R := row i
  ∑ a ∈ Finset.range (R.n + 1),
    (highCurve i).increment a * responsePacking i a * tail R a

def density (i : Fin 4) : ℚ :=
  cover (row i) (cutoff (row i)) + highMass i

theorem highMass_nonneg (i : Fin 4) : 0 ≤ highMass i := by
  fin_cases i <;> native_decide

theorem hash1_density_lt_six : density 0 < (6 : ℚ) / 2 ^ 128 := by
  native_decide

theorem hash2_density_lt_six : density 1 < (6 : ℚ) / 2 ^ 128 := by
  native_decide

theorem hash3_density_lt_six : density 2 < (6 : ℚ) / 2 ^ 128 := by
  native_decide

theorem hash4_density_lt_six : density 3 < (6 : ℚ) / 2 ^ 128 := by
  native_decide

theorem density_lt_six (i : Fin 4) : density i < (6 : ℚ) / 2 ^ 128 := by
  fin_cases i
  · exact hash1_density_lt_six
  · exact hash2_density_lt_six
  · exact hash3_density_lt_six
  · exact hash4_density_lt_six

end Lfzk.V1StrongV7Numeric
