import Lfzk.GradedCost
import Lfzk.NizkZk

/-!
# A compact graded agreement curve at the v8 hash geometry

The six rational weights were found by an untrusted numerical search.
All facts used below are closed Lean checks. `GradedCircuitV8` instantiates
the compiled two-field potential theorem at this row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.GradedV8Hash

open Finset LigeroFamily LigeroFamily.PotentialProfile
  LigeroFamily.PolicyDoublyProfiledSoundnessClassifier
  Lfzk.CertifiedV1

private def steps : Finset ℕ := [2233, 2238, 2245, 2255, 2270, 2300].toFinset

private def weight : ℕ → ℚ
  | 2233 => 1075 / 4096
  | 2238 => 1046 / 4096
  | 2245 => 896 / 4096
  | 2255 => 641 / 4096
  | 2270 => 365 / 4096
  | 2300 => 73 / 4096
  | _ => 0

private theorem steps_pos : ∀ a ∈ steps, 0 < a := by
  simp [steps]

private theorem weight_nonneg : ∀ a ∈ steps, 0 ≤ weight a := by
  norm_num [steps, weight]

private theorem weight_total : ∑ a ∈ steps, weight a ≤ 1 := by
  norm_num [steps, weight]

/-- A checked monotone potential at the registered v8 hash geometry. -/
def curve : Curve v8Hash.params.row.n :=
  weightedStepCurve _ steps weight steps_pos weight_nonneg weight_total

abbrev challengeCost : ℚ := Lfzk.GradedCost.challenge v8Hash curve

abbrev queryCost : ℚ := Lfzk.GradedCost.query v8Hash curve

/-- Closed upper bound for the graded combination-challenge density. -/
theorem challengeCost_le : challengeCost ≤ (1804 : ℚ) / 2 ^ 128 := by
  native_decide

/-- Closed upper bound for the residual column-query density. -/
theorem queryCost_le : queryCost ≤ (1134 : ℚ) / 2 ^ 128 := by
  native_decide

/-- A checked envelope for the two terminal charges of this curve. -/
theorem terminalCost_le :
    challengeCost + queryCost ≤ (2938 : ℚ) / 2 ^ 128 := by
  have hc := challengeCost_le
  have hq := queryCost_le
  linarith

/-- The graded terminal envelope improves the registered one-cutoff cost. -/
theorem terminalCost_lt_registered :
    challengeCost + queryCost < v8Hash.params.ligeroDensity := by
  exact lt_of_le_of_lt terminalCost_le (by native_decide)

/-- The hash side's field slots plus graded terminal cost at `logv = 5`.
This is arithmetic for the concrete row; `GradedCircuitV8` supplies the
deployed FS extraction theorem. -/
theorem coreCost_le :
    (v8Hash.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity v8Hash 5 +
      challengeCost + queryCost ≤ (5660 : ℚ) / 2 ^ 128 := by
  have ht := terminalCost_le
  have hf :
      (v8Hash.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity v8Hash 5 =
        (2722 : ℚ) / 2 ^ 128 := by
    native_decide
  linarith

theorem coreCost_le_115 :
    (v8Hash.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity v8Hash 5 +
      challengeCost + queryCost ≤ (1 : ℚ) / 2 ^ 115 := by
  exact coreCost_le.trans (by norm_num)

end Lfzk.GradedV8Hash
