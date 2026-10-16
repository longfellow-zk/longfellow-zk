import Lfzk.GradedCost
import Lfzk.SoundnessAudit

/-!
# Six-step graded curves for the four registered v7 hash geometries

The weights were selected by an untrusted linear program and rounded to
denominator 4096. Every curve condition and cost inequality is checked
below. `GradedCircuitV7` instantiates the compiled two-field potential
theorem at these rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.GradedV7Hash

open Finset LigeroFamily LigeroFamily.PotentialProfile
  LigeroFamily.PolicyDoublyProfiledSoundnessClassifier
  Lfzk.CertifiedV1

def row (i : Fin 4) : Row := Lfzk.SoundnessAudit.v7HashRow i

theorem row_valid (i : Fin 4) : (row i).Valid := by
  fin_cases i
  · exact v7Hash1_valid
  · exact v7Hash2_valid
  · exact v7Hash3_valid
  · exact v7Hash4_valid

theorem row_openings_pos (i : Fin 4) : 0 < (row i).params.row.openings := by
  fin_cases i
  · exact v7Hash1_openings_pos
  · exact v7Hash2_openings_pos
  · exact v7Hash3_openings_pos
  · exact v7Hash4_openings_pos

private def steps (i : Fin 4) : Finset ℕ :=
  (match i.val with
    | 0 => [1766, 1771, 1778, 1788, 1803, 1833]
    | 1 => [1815, 1820, 1827, 1837, 1852, 1882]
    | 2 => [1833, 1838, 1845, 1855, 1870, 1900]
    | _ => [1879, 1884, 1891, 1901, 1916, 1946]).toFinset

private def weights (i : Fin 4) : List (ℕ × ℕ) :=
  match i.val with
  | 0 => [(1766, 1317), (1771, 1162), (1778, 868), (1788, 511),
      (1803, 213), (1833, 25)]
  | 1 => [(1815, 1287), (1820, 1149), (1827, 874), (1837, 528),
      (1852, 229), (1882, 29)]
  | 2 => [(1833, 1276), (1838, 1145), (1845, 876), (1855, 534),
      (1870, 235), (1900, 30)]
  | _ => [(1879, 1249), (1884, 1133), (1891, 881), (1901, 549),
      (1916, 250), (1946, 34)]

private def weight (i : Fin 4) (a : ℕ) : ℚ :=
  ((((weights i).find? (fun p => p.1 == a)).map Prod.snd).getD 0 : ℚ) / 4096

private theorem steps_pos (i : Fin 4) : ∀ a ∈ steps i, 0 < a := by
  fin_cases i <;> simp [steps]

private theorem weight_nonneg (i : Fin 4) :
    ∀ a ∈ steps i, 0 ≤ weight i a := by
  fin_cases i <;> native_decide

private theorem weight_total (i : Fin 4) :
    ∑ a ∈ steps i, weight i a ≤ 1 := by
  fin_cases i <;> native_decide

/-- A checked potential for each registered v7 hash row. -/
def curve (i : Fin 4) : Curve (row i).params.row.n :=
  weightedStepCurve _ (steps i) (weight i)
    (steps_pos i) (weight_nonneg i) (weight_total i)

abbrev challengeCost (i : Fin 4) : ℚ :=
  Lfzk.GradedCost.challenge (row i) (curve i)

abbrev queryCost (i : Fin 4) : ℚ :=
  Lfzk.GradedCost.query (row i) (curve i)

def challengeNumerator (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 1684
  | 1 => 1676
  | 2 => 1612
  | _ => 1612

def queryNumerator (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 771
  | 1 => 888
  | 2 => 857
  | _ => 914

def terminalNumerator (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 2455
  | 1 => 2564
  | 2 => 2469
  | _ => 2526

/-- The checked per-challenge density, scaled to the 128-bit field. -/
theorem challengeCost_le (i : Fin 4) :
    challengeCost i ≤ (challengeNumerator i : ℚ) / 2 ^ 128 := by
  fin_cases i <;> native_decide

/-- The checked residual per-query density. -/
theorem queryCost_le (i : Fin 4) :
    queryCost i ≤ (queryNumerator i : ℚ) / 2 ^ 128 := by
  fin_cases i <;> native_decide

/-- Checked challenge plus query densities, scaled to the 128-bit field. -/
theorem terminalCost_le (i : Fin 4) :
    challengeCost i + queryCost i ≤
      (terminalNumerator i : ℚ) / 2 ^ 128 := by
  have hc := challengeCost_le i
  have hq := queryCost_le i
  have hn : terminalNumerator i =
      challengeNumerator i + queryNumerator i := by
    fin_cases i <;> rfl
  rw [hn]
  push_cast
  linarith

/-- All four graded curves strictly improve their registered cutoff costs. -/
theorem terminalCost_lt_registered (i : Fin 4) :
    challengeCost i + queryCost i < (row i).params.ligeroDensity := by
  exact lt_of_le_of_lt (terminalCost_le i) (by fin_cases i <;> native_decide)

/-- The field slots and graded terminal charge for each registered hash
profile fit at the 115-bit integer level.  The deployed FS composition is
proved separately from this arithmetic statement. -/
theorem coreCost_le_115 (i : Fin 4) :
    ((row i).cardCand : ℚ) *
        Lfzk.NizkZk.zkFieldDensity (row i)
          (Lfzk.SoundnessAudit.v7HashLogv i) +
      challengeCost i + queryCost i ≤ (1 : ℚ) / 2 ^ 115 := by
  have ht := terminalCost_le i
  have hn :
      ((row i).cardCand : ℚ) *
          Lfzk.NizkZk.zkFieldDensity (row i)
            (Lfzk.SoundnessAudit.v7HashLogv i) +
        (terminalNumerator i : ℚ) / 2 ^ 128 ≤ (1 : ℚ) / 2 ^ 115 := by
    fin_cases i <;> native_decide
  linarith

end Lfzk.GradedV7Hash
