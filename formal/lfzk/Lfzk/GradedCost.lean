import Lfzk.CertifiedV1
import LigeroFamily.Soundness.PolicyPotential
import LigeroFamily.Soundness.PotentialProfile

/-!
# Shared numerical interface for a certified V1 row and a graded curve

The two densities are exactly those used by `CompiledZkSide.terminalPotential`.
Concrete row certificates and the compiled-side budget adapter both refer
to these definitions, avoiding a second transcription of the formulas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.GradedCost

open Finset LigeroFamily LigeroFamily.PotentialProfile
  LigeroFamily.PolicyDoublyProfiledSoundnessClassifier
  Lfzk.CertifiedV1

def challenge (R : Row) (ψ : Curve R.params.row.n) : ℚ :=
  ∑ a ∈ range (R.params.row.n + 1), ψ.increment a *
    gradedTail
      (R.params.row.failureProfileAt R.params.row.fieldSize)
      (R.params.row.arithProfile)
      (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
        R.params.row.fieldSize R.params.row.g)
      R.params.row.fieldSize R.params.row.e R.params.row.g a

def query (R : Row) (ψ : Curve R.params.row.n) : ℚ :=
  ψ.queryCost (fun a => hypergeometricRatio a R.params.row.n
    R.params.row.openings)

end Lfzk.GradedCost
