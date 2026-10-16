import Lfzk.GradedCost
import Lfzk.CertifiedHahn

/-!
# Graded terminal budgets for the signature sides

The v7 Hahn/Delsarte signature and v8 signature contributions are already
small relative to their hash sides.  A single-step curve at each certified
query cover reproduces the registered challenge and query bounds, while
using the same extraction-first potential interface as the hash curves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.GradedSignature

open Finset LigeroFamily LigeroFamily.PotentialProfile
  LigeroFamily.PolicyDoublyProfiledSoundnessClassifier
  Lfzk.CertifiedV1

/-- `false` selects the v7 Hahn/Delsarte signature, `true` the v8 signature. -/
def row (v8 : Bool) : Row := if v8 then v8Sig else v7SigHahn

def curve (v8 : Bool) : Curve (row v8).params.row.n :=
  stepCurve _ ((row v8).params.row.queryCover + 1) (by omega)

abbrev challengeCost (v8 : Bool) : ℚ :=
  Lfzk.GradedCost.challenge (row v8) (curve v8)

abbrev queryCost (v8 : Bool) : ℚ :=
  Lfzk.GradedCost.query (row v8) (curve v8)

/-- The challenge cost is no larger than the registered two profile tails. -/
theorem challengeCost_le (v8 : Bool) :
    challengeCost v8 ≤ (row v8).params.row.fail +
      (row v8).params.row.arith := by
  cases v8 <;> native_decide

/-- The residual query cost is no larger than the registered cover. -/
theorem queryCost_le (v8 : Bool) :
    queryCost v8 ≤ (row v8).params.row.cover := by
  cases v8 <;> native_decide

theorem terminalCost_le_registered (v8 : Bool) :
    challengeCost v8 + queryCost v8 ≤ (row v8).params.ligeroDensity := by
  have hc := challengeCost_le v8
  have hq := queryCost_le v8
  change challengeCost v8 + queryCost v8 ≤
    ((row v8).params.row.fail + (row v8).params.row.arith) +
      (row v8).params.row.cover
  linarith

end Lfzk.GradedSignature
