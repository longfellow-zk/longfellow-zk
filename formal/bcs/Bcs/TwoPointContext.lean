import Bcs.TotalOracleCommit

/-! Cut-trace context stability under two answers naming one commitment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracleCommit.Setup

open Bcs.TotalOracle

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D]
  [DecidableEq Pt] [DecidableEq Key]
  {tA N L TM : ℕ}

/-- A committed key's cut trace is unchanged when two oracle answers at
points naming that same key are replaced.  The cut precedes the first query
of either point, irrespective of their order. -/
theorem ctxAt_off_two
    (S : Bcs.TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)
    (mt : Fin TM → D) (H H' : Pt → C) (x y : Pt)
    (hkey : S.key x = S.key y)
    (h : ∀ z, z ≠ x → z ≠ y → H z = H' z) :
    (S.atOracle H').ctxAt mt emptyTape (S.key x) =
      (S.atOracle H).ctxAt mt emptyTape (S.key x) := by
  let mid : Pt → C := fun z => if z = x then H' z else H z
  have hx : AgreeOff x H mid := by
    intro z hz
    simp [mid, hz]
  have hy : AgreeOff y mid H' := by
    intro z hz
    by_cases hzx : z = x
    · simp [mid, hzx]
    · simp [mid, hzx, h z hzx hz]
  have h₁ := S.ctxAt_off mt H mid x hx
  have h₂ := S.ctxAt_off mt mid H' y hy
  rw [← hkey] at h₂
  exact h₂.trans h₁

end Bcs.TotalOracleCommit.Setup
